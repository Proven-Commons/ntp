#!/usr/bin/env python3
"""Draft NTP wire-contract oracle. No authentication or era inference.

JSON lines in: {"packet_hex": "...", "mac_length": 0}.
JSON lines out: the fixture's expected object, or {"error": "..."}.
RFC 5905 sections 6/7.3; RFC 7822 section 3. See WIRE-CONTRACT.md.
"""

import json
import sys
from fractions import Fraction


class WireError(ValueError):
    """An input outside this explicit draft contract."""


def read_header(packet):
    if len(packet) < 48:
        raise WireError("short_header")
    first = packet[0]
    if (first >> 3) & 7 not in (3, 4):
        raise WireError("unsupported_version")
    signed = lambda n: n if n < 128 else n - 256
    timestamps = []
    for offset in (16, 24, 32, 40):
        raw = int.from_bytes(packet[offset:offset + 8], "big")
        timestamps.append({"raw": raw, "seconds": raw >> 32,
                           "fraction": raw & 0xffffffff, "unknown": raw == 0})
    return {"leap": first >> 6, "version": (first >> 3) & 7, "mode": first & 7,
            "stratum": packet[1], "poll": signed(packet[2]),
            "precision": signed(packet[3]),
            "root_delay_bits": int.from_bytes(packet[4:8], "big"),
            "root_dispersion_bits": int.from_bytes(packet[8:12], "big"),
            "reference_id_hex": packet[12:16].hex(), "timestamps": timestamps}


def timestamp_unix(raw, era):
    """Exact Unix seconds, given an external era, or None for unknown."""
    if type(raw) is not int or not 0 <= raw < 2 ** 64:
        raise WireError("timestamp_range")
    if type(era) is not int:
        raise WireError("era_required")
    if raw == 0:
        return None
    return Fraction(era * 2 ** 32 + (raw >> 32) - 2208988800) + Fraction(raw & 0xffffffff, 2 ** 32)


def decode(packet, mac_length):
    """Frame using caller-supplied MAC length; never guess from tail bytes."""
    if type(mac_length) is not int or mac_length not in (0, 4, 20, 24):
        raise WireError("unsupported_mac_length")
    header = read_header(packet)
    end = len(packet) - mac_length
    if end < 48:
        raise WireError("short_mac")
    offset = 48
    extensions = []
    while offset < end:
        if end - offset < 4:
            raise WireError("short_extension_header")
        field_type = int.from_bytes(packet[offset:offset + 2], "big")
        length = int.from_bytes(packet[offset + 2:offset + 4], "big")
        if length < 16:
            raise WireError("short_extension")
        if length % 4:
            raise WireError("unaligned_extension")
        if length > end - offset:
            raise WireError("extension_overrun")
        extensions.append({"offset": offset, "type": field_type, "length": length,
                           "value_and_padding_hex": packet[offset + 4:offset + length].hex()})
        offset += length
    if not mac_length and extensions and extensions[-1]["length"] < 28:
        raise WireError("short_final_extension_without_mac")
    return {"header": header, "extensions": extensions,
            "mac_hex": packet[end:].hex() if mac_length else "",
            "mac_length": mac_length}


def answer(request):
    try:
        packet = bytes.fromhex(request["packet_hex"])
        return decode(packet, request["mac_length"])
    except WireError as e:
        return {"error": str(e)}
    except (KeyError, TypeError, ValueError):
        return {"error": "malformed_request"}


def main():
    for line in sys.stdin:
        try:
            request = json.loads(line)
        except ValueError:
            result = {"error": "malformed_request"}
        else:
            result = answer(request)
        print(json.dumps(result, sort_keys=True))


if __name__ == "__main__":
    main()
