#!/usr/bin/env python3
"""Differential tests: the Lean reader and writer of the NTP packet
against a model of RFC 5905 and RFC 7822, and against other NTP
implementations.

The tool answers `decode`, `encode`, `unix` and `fromunix` requests
(see the header of Main.lean). Its answers are checked three ways.

1. Against the model, written in Python from RFC 5905 (Figure 8,
   sections 6, 7.3 and 9.2), RFC 7822 (sections 3 and 7.5.1.3 to
   7.5.1.4) and Ntp/Spec/Defs.lean, sharing nothing with the Lean code:
   - `valid` and `packet_bytes` are Ntp/Spec/Defs.lean's `Valid` and
     `packetBytes`: the header of Figure 8, big-endian; each extension
     field its Field Type, its Length (the whole field) and its Value and
     Padding, of a Length that is a multiple of 4 from 16 to 65532; a MAC
     of none, 20 or 24 octets, or four zero octets (the crypto-NAK) with
     no field; no field in version 3; a last field of at least 28 octets
     when there is no MAC;
   - `decode_spec` finds the packet that `Ntp.Spec.decode_iff` says the
     decoder must give, from those two alone: for each MAC length that
     `valid` allows, it splits the octets before the MAC into fields by
     their Length fields, and keeps the packets that are valid and whose
     octets are the input. There is at most one, by `Ntp.Spec.decode_iff`,
     and the script fails if it finds two;
   - `read` is the one-pass reading SPEC.md describes ("Reading the
     octets after the header"): four zero octets are a crypto-NAK; in
     version 3 the MAC is 0, 20 or 24 octets; in version 4, while more
     than 24 octets are left, a field starts there. On every input it
     must give what `decode_spec` gives (a check of SPEC.md's claim that
     the rule accepts exactly the valid packets), and it gives the reason
     the record counts for each refusal. With switches, each named for a
     choice of one of the oracles below, it reads as that oracle does;
   - `to_unix` and `from_unix` are RFC 5905 section 6 in exact rational
     arithmetic: "s = era * 2^(32) + timestamp", less the 2,208,988,800
     seconds from 1900 to 1970 (Figure 4), with "era = s / 2^(32)"
     rounding down; the raw value 0, "unknown or unsynchronized time",
     has no Unix time; nor does a value of 2^64 or more, and a fraction
     of 2^32 or more has no timestamp;
   - the request parsing and the output of the header of Main.lean.
   The model must give the answers Ntp/Spec.lean states in `examples` and
   `rejects`. Every answer of the tool must equal the model's.

2. Against other readers of the packet, on every `decode` input. Each
   gives its answer in its own way, and the script brings it to one
   form: refused, or the header fields, the extension fields (type and
   octets), the MAC, and the octets it shows nowhere. Each oracle
   chooses differently from this reader in places, and the model has a
   switch for each such choice, named in ORACLE_RULES. The model with
   all of an oracle's switches on must give that oracle's answer on
   every input, whether or not the tool agrees; any other answer is a
   failure. Where the tool and an oracle differ, the difference is
   counted under the smallest set of that oracle's switches with which
   the model gives the oracle's answer; a difference no set explains is
   a failure. The oracles:
   - ntpd-rs: the packet parser of its ntp-proto crate,
     `NtpPacket::deserialize`, in the small program in tests/ntpd-rs
     (its Cargo.lock pins every crate), built with `cargo build
     --release --locked`;
   - NTPsec: `ntp.packet.SyncPacket.analyze`, from the Python module of
     NTPsec (Debian and Ubuntu package python3-ntp);
   - Wireshark: its NTP dissector, through tshark, which reads a
     capture of every input with the dissector registered for a user
     link type, and prints PDML; a packet is refused when Wireshark
     marks it malformed or adds an expert note to it, or reads it as a
     control or private message (modes 6 and 7);
   - ntplib, for the header fields only: `NTPPacket.from_data`, with the
     fields as it keeps them (root delay and dispersion divided by 2^16,
     timestamps as floats).
   An oracle that is not installed, or not at the pinned version, is
   left out, and the record says so. chrony's own parser is not among
   them: the session that wrote these tests was not permitted to build
   chrony's downloaded source for a harness, so it was dropped, and the
   record says that too.

   The `unix` answers are also checked against RFC 5905 Figure 4, whose
   rows give dates with their Modified Julian Day, era and era offset,
   with two errata applied (4025: the MJD of 1 Jan 0; 6524: the era
   offset of 1 Jan 1), and against Python's datetime module (the
   proleptic Gregorian calendar, with no leap seconds) wherever the
   date is within its years 1 to 9999.

3. Against the vectors of Proven-Commons/ntp pull request 3, a wire
   contract and 79 vectors by orda-aska (commit cc5dab4, file
   tests/wire_vectors.jsonl, copied as tests/ntp-3-wire-vectors.jsonl and
   read as data only). Each vector gives a packet, a MAC length chosen
   by the caller, and the expected answer. The tool reads the packet by
   its own rule, and each difference is counted under the switches with
   which the model gives the vector's answer, as for the oracles.

Inputs come from a recorded seed:
- the inputs of Ntp/Spec.lean's `examples` and `rejects`;
- every value of the first octet (leap, version and mode) in eight
  packets of every shape; every value of every header octet in the
  server reply; headers from random fields and random octets;
- packets of 0 to 5 extension fields of random types (the NTS types,
  others, and types whose two octets differ), random bodies and lengths
  from 16 to 65532, with no MAC, a MAC of 20 or 24 octets, or a
  crypto-NAK, in versions 3 and 4;
- such packets with one rule broken: a field of Length 0 to 12, a Length
  that is not a multiple of 4, a Length running 4 or 1000 octets past
  the end, or to 65532 or 65535 (CVE-2014-9750's flaw, at the level of
  the field's own Length), a last field of 16 to 24 octets with no MAC,
  a MAC of 8 to 16, 21 to 23 or 28 octets, four octets that are not
  zero, a crypto-NAK after a field, a field in version 3, another
  version or mode, an octet more or less;
- Autokey fields laid out as RFC 5906 Figure 7 whose Value Length runs
  past the field, as in CVE-2014-9750: each must be read by its own
  Length, with its octets unchanged, and the record counts them;
- after the client request and after a version 3 header, tails of every
  length from 0 to 80: zeros, random octets, all ones, and one field of
  that length; a field of every Length from 0 to 80 with and without a
  20-octet MAC after it;
- truncations of valid packets at every length, and random changes of
  valid packets: an octet changed, a bit flipped, octets inserted or
  removed, a Length field changed;
- `unix` over eras -1, 0, 1 and 2 with the raw values 0, 1, 2^32 - 1,
  2^32, 2^64 - 1, 2208988800 * 2^32 and others, the 2036 rollover,
  values of 2^64 and more, random eras and values, and the rows of
  Figure 4; `fromunix` of every Unix time `unix` gave, at and around
  the first instant of each era, with fractions of 2^32 and more, and
  random;
- `encode` of every packet the model reads, and of packets each with
  one field out of range or one rule broken;
- the 79 vectors of pull request 3;
- malformed requests, which the tool must answer with `error`, odd but
  well-formed ones, and the command line.
Every seventh request ends in CR LF. The record gives a SHA-256 of the
requests, so that a rerun with the same seed and count can be checked
to have the same inputs.

    python3 tests/run_tests.py [--seed N] [--count N] [--no-oracles] [--no-build]

`--count` is the number of random packets; a fifth as many random
headers, as many packets with a rule broken and as many changed
packets, a hundredth as many cut at every length, and half as many
random `unix` and as many random `fromunix` requests are made.
`--no-oracles` compares the tool with the model alone, as
tests/plant_bugs.py does, and leaves out Figure 4, datetime and the
vectors of pull request 3 too. The script builds the executable with `lake
build ntp` first, or, with `--no-build`, takes the one in .lake/build/bin
as it is; either way it runs a copy. It writes tests/TEST-RESULTS.md and
exits non-zero if any check fails.
"""

import argparse
import collections
import datetime
import hashlib
import itertools
import json
import math
import os
import random
import re
import shutil
import struct
import subprocess
import sys
import tempfile
import threading
import time
from fractions import Fraction
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
BUILT_EXE = ROOT / ".lake" / "build" / "bin" / "ntp"
TESTS = ROOT / "tests"
RESULTS = TESTS / "TEST-RESULTS.md"
VECTORS = TESTS / "ntp-3-wire-vectors.jsonl"
NTPDRS_SOURCE = TESTS / "ntpd-rs"
NTPDRS_TARGET = ROOT / ".lake" / "oracles" / "ntpd-rs"
TIMEOUT = 3600
# The pinned versions: an oracle at another version is left out.
NTP_PROTO_PINNED = "1.9.0"
NTPSEC_PINNED = "1.2.2"
TSHARK_PINNED = "4.2.2"
NTPLIB_PINNED = "0.4.0"
# The largest frame tshark reads (WTAP_MAX_PACKET_SIZE_STANDARD).
TSHARK_MAX = 262144
# Requests are split among this many `ntp serve` processes.
JOBS = max(1, min(4, os.cpu_count() or 1))
EXE = None

# ---------------------------------------------------------------------
# The model: Ntp/Spec/Defs.lean, from RFC 5905 and RFC 7822.

T16, T32, T64 = 1 << 16, 1 << 32, 1 << 64
# Ntp.Spec.unixEpoch: RFC 5905 Figure 4, "1 Jan 1970 ... 2,208,988,800 First
# day UNIX".
UNIX_EPOCH = 2208988800

Header = collections.namedtuple(
    "Header", "leap version mode stratum poll precision root_delay root_dispersion ref_id "
              "reference origin receive transmit")


def be(bs):
    return int.from_bytes(bs, "big")


def be_bytes(w, n):
    """Ntp.Spec.beBytes: n as w octets, most significant first, each
    n / 256^i % 256."""
    return bytes((n // 256 ** i) % 256 for i in reversed(range(w)))


def signed(octet):
    """An octet as an 8-bit two's complement integer."""
    return octet - 256 if octet >= 128 else octet


def header_bytes(h):
    """Ntp.Spec.headerBytes: Figure 8. LI, VN and Mode in the first octet,
    two, three and three bits from the top; Poll and Precision in two's
    complement (Ntp.Spec.signedByte)."""
    return (bytes([(h.leap * 64 + h.version * 8 + h.mode) % 256, h.stratum % 256, h.poll % 256,
                   h.precision % 256])
            + be_bytes(4, h.root_delay) + be_bytes(4, h.root_dispersion) + be_bytes(4, h.ref_id)
            + be_bytes(8, h.reference) + be_bytes(8, h.origin) + be_bytes(8, h.receive)
            + be_bytes(8, h.transmit))


def ext_length(e):
    """Ntp.Spec.ExtField.length: the Length field counts the whole field."""
    return len(e[1]) + 4


def ext_bytes(e):
    """Ntp.Spec.extBytes: RFC 7822 Figure 14."""
    return be_bytes(2, e[0]) + be_bytes(2, ext_length(e)) + e[1]


def packet_bytes(p):
    """Ntp.Spec.packetBytes: the header, the fields in order, the MAC."""
    h, exts, mac = p
    return header_bytes(h) + b"".join(ext_bytes(e) for e in exts) + mac


def header_valid(h):
    """Ntp.Spec.HeaderValid."""
    return (0 <= h.leap < 4 and h.version in (3, 4) and 1 <= h.mode <= 5 and 0 <= h.stratum < 256
            and -128 <= h.poll < 128 and -128 <= h.precision < 128
            and all(0 <= x < T32 for x in (h.root_delay, h.root_dispersion, h.ref_id))
            and all(0 <= x < T64 for x in (h.reference, h.origin, h.receive, h.transmit)))


def ext_valid(e):
    """Ntp.Spec.ExtValid: RFC 7822 section 3."""
    n = ext_length(e)
    return 0 <= e[0] < T16 and 16 <= n and n % 4 == 0 and n < T16


def mac_valid(exts, mac):
    """Ntp.Spec.MacValid: none, 20 or 24 octets, or the crypto-NAK alone."""
    return mac == b"" or len(mac) in (20, 24) or (mac == bytes(4) and not exts)


def valid(p):
    """Ntp.Spec.Valid."""
    h, exts, mac = p
    return (header_valid(h) and all(ext_valid(e) for e in exts) and (h.version != 3 or not exts)
            and mac_valid(exts, mac) and (mac != b"" or not exts or 28 <= ext_length(exts[-1])))


def header_of(b, poll_unsigned=False):
    """The fields of the first 48 octets, as Figure 8 lays them out."""
    return Header(b[0] >> 6, (b[0] >> 3) & 7, b[0] & 7, b[1], b[2] if poll_unsigned else signed(b[2]),
                  signed(b[3]), be(b[4:8]), be(b[8:12]), be(b[12:16]), be(b[16:24]), be(b[24:32]),
                  be(b[32:40]), be(b[40:48]))


def decode_spec(b):
    """The packet p with Valid p and packetBytes p = b, or None: what
    Ntp.Spec.decode_iff says the decoder gives. The MAC is one of the lengths
    MacValid allows; the octets between the header and the MAC are then
    fields, one after another, each as long as its Length field says,
    since that is how packetBytes writes them."""
    if len(b) < 48:
        return None
    h, tail = header_of(b), b[48:]
    found = []
    for m in (0, 4, 20, 24):
        if m > len(tail):
            continue
        body, mac = tail[:len(tail) - m], tail[len(tail) - m:]
        exts, i = [], 0
        while i < len(body):
            if len(body) - i < 4:
                break
            n = be(body[i + 2:i + 4])
            if n < 4 or i + n > len(body):
                break
            exts.append((be(body[i:i + 2]), body[i + 4:i + n]))
            i += n
        if i != len(body):
            continue
        p = (h, tuple(exts), mac)
        if valid(p) and packet_bytes(p) == b:
            found.append(p)
    if len(found) > 1:
        raise AssertionError(f"two packets for {b.hex()}: Ntp.Spec.decode_iff says at most one")
    return found[0] if found else None


# Why the model refuses a packet: the rule of `read` that refuses it.
WHY_SHORT = "fewer than 48 octets (RFC 5905 7.3: the header is 12 words)"
WHY_VERSION = "a version other than 3 and 4"
WHY_MODE = "mode 0, 6 or 7 (RFC 5905 Figure 10)"
WHY_V3 = ("version 3, with octets after the header that are not a MAC of 20 or 24 octets or a "
          "crypto-NAK (this reader's choice: the MACs of NTPv4, and no extension fields, which RFC "
          "7822 section 3 gives to NTPv4; RFC 1305's own authenticator is 12 octets)")
WHY_NAK = "four octets after the header that are not zero (RFC 5905 9.2: the crypto-NAK is zeros)"
WHY_SMALL = "a field of Length below 16 (RFC 7822 section 3)"
WHY_ALIGN = "a field Length that is not a multiple of 4 (RFC 7822 section 3)"
WHY_PAST = ("a field Length past the end of the packet (CVE-2014-9750's flaw, at the level of the "
            "field's own Length)")
WHY_NAK_FIELDS = "four zero octets after extension fields: the crypto-NAK is a packet's only tail"
WHY_LEFT_WORDS = ("8, 12 or 16 octets left after the fields: not a MAC (RFC 7822 7.5.1.3), and a last "
                  "field without a MAC is at least 28 (7.5.1.4)")
WHY_LEFT_4 = "four octets left after the fields that are not zero: not a crypto-NAK"
WHY_LEFT_21 = "21 to 23 octets left: not a MAC of 20 or 24 octets (RFC 7822 section 1)"
WHY_LEFT_ODD = "1 to 19 octets left that are not a whole number of words (RFC 7822 section 3)"

# Each oracle's choices where it differs from this reader, as switches
# of `read`.
NR_MODES = "ntpd-rs reads every mode, 0, 6 and 7 too, with the header of Figure 8"
NR_MIN4 = ("ntpd-rs takes an extension field of 4 to 12 octets: its minimum is 4 "
           "(V4_UNENCRYPTED_MINIMUM_SIZE), where RFC 7822 asks for 16")
NR_MAC = ("ntpd-rs takes any 4 to 24 octets left after the extension fields as the MAC, whatever "
          "they hold (Mac::deserialize): four octets that are not zero, a crypto-NAK after fields, "
          "8 to 16 octets that RFC 7822 7.5.1.4 rules out, and 21 to 23")
NR_V3 = "ntpd-rs takes any 4 to 24 octets after a version 3 header as the MAC"
NR_NTS = ("ntpd-rs refuses an NTS Cookie Placeholder (0x0304) whose body is not zero, and an NTS "
          "Authenticator and Encrypted Extension Fields field (0x0404) whose nonce and ciphertext "
          "lengths run past it (RFC 8915 5.5 and 5.6)")
NS_LEN4 = "NTPsec refuses a packet whose length is not a multiple of 4"
NS_VERSIONS = "NTPsec reads every version"
NS_MODES = "NTPsec reads every mode with the header of Figure 8"
NS_POLL = "NTPsec reads Poll as unsigned (struct format B; RFC 5905 7.3 says signed)"
NS_FIELDS = ("NTPsec reads an extension field as a 32-bit type and a 32-bit length of the value after "
             "them, with no padding or minimum, cut short at the end of the packet "
             "(SyncPacket.analyze), not as RFC 7822 Figure 14 lays it out")
NS_TAIL = ("NTPsec takes four octets left after the fields as a crypto-NAK whatever they hold, fields "
           "or not; refuses 8, 12 or 16; and drops any other number of octets but 0, 20 and 24 "
           "without a word")
NS_V3 = "NTPsec reads version 3 as version 4, extension fields too"
WS_VERSIONS = "Wireshark reads every version"
WS_MODE0 = "Wireshark reads mode 0 with the header of Figure 8"
WS_TAIL = ("Wireshark splits the octets after the header its own way (packet-ntp.c, dissect_ntp_std): "
           "fields while 16 or more octets are left, each of a Length of 16 or more that fits; then, "
           "when 1 to 19 octets are left that are not a crypto-NAK, it gives the last field back to "
           "the MAC; whatever is left is the MAC, of any length and content; a Length that is not a "
           "multiple of 4 gets an expert note; in every version")
NL_VERSIONS = "ntplib reads every version"
NL_MODES = "ntplib reads every mode"
NL_TAIL = "ntplib reads the header only, whatever follows it"
NL_POLL = "ntplib reads Poll as unsigned (struct format B)"
P_MACLEN = ("ntp#3 takes the MAC length from the caller (mac_length), so the octets before it must "
            "all be extension fields: with mac_length 0, a tail of 20 or 24 octets is a short last "
            "field, not a MAC (WIRE-CONTRACT.md)")
P_MAC4 = "ntp#3 takes a 4-octet MAC of any value, after extension fields too"
P_V3 = "ntp#3 reads extension fields in version 3"
P_MODES = "ntp#3 reads every mode"

ORACLE_RULES = {
    "ntpd-rs": [NR_MODES, NR_MIN4, NR_MAC, NR_V3, NR_NTS],
    "NTPsec": [NS_LEN4, NS_VERSIONS, NS_MODES, NS_POLL, NS_FIELDS, NS_TAIL, NS_V3],
    "Wireshark": [WS_VERSIONS, WS_MODE0, WS_TAIL],
    "ntplib": [NL_VERSIONS, NL_MODES, NL_TAIL, NL_POLL],
    "ntp#3": [P_MACLEN, P_MAC4, P_V3, P_MODES],
}


def relevant(rule, b):
    """Whether a switch can change the reading of b at all: a rule about
    the version, the mode, Poll, the length or version 3 cannot when b
    has nothing it applies to. Used only to search fewer sets."""
    if len(b) < 48:
        return rule == NS_LEN4
    version, mode = (b[0] >> 3) & 7, b[0] & 7
    if rule in (NS_VERSIONS, NL_VERSIONS, WS_VERSIONS):
        return version not in (3, 4)
    if rule in (NR_MODES, NS_MODES, NL_MODES, P_MODES):
        return not 1 <= mode <= 5
    if rule == WS_MODE0:
        return mode == 0
    if rule in (NS_POLL, NL_POLL):
        return b[2] >= 128
    if rule == NS_LEN4:
        return len(b) % 4 != 0
    if rule in (NR_V3, NS_V3, P_V3):
        return version == 3
    return True


def nts_fits(body):
    """ntpd-rs's RawEncryptedField::from_message_bytes: a 16-bit nonce
    length, a 16-bit ciphertext length, the nonce, padding to a word, and
    the ciphertext, all within the body."""
    if len(body) < 4:
        return False
    nonce, ciphertext = be(body[0:2]), be(body[2:4])
    if nonce > len(body) - 4:
        return False
    start = 4 + ((nonce + (-nonce) % 4) % T16)
    return start + ciphertext <= len(body)


def why_left(left, fields):
    """Why the octets left after the fields are not a MAC."""
    n = len(left)
    if n == 4:
        return WHY_NAK_FIELDS if left == bytes(4) else (WHY_LEFT_4 if fields else WHY_NAK)
    if n in (8, 12, 16):
        return WHY_LEFT_WORDS
    if 21 <= n <= 23:
        return WHY_LEFT_21
    return WHY_LEFT_ODD


def ok(h, fields, mac, rest=0):
    return (h, tuple(fields), bytes(mac), rest)


def read(b, rules=frozenset(), mac_length=None):
    """The packet, as (header, fields, MAC, octets shown nowhere), or
    None; and why it is refused. With no rules, the one-pass reading of
    SPEC.md; each rule switches on one choice of an oracle."""
    R = rules
    if len(b) < 48:
        return None, WHY_SHORT
    if NS_LEN4 in R and len(b) % 4:
        return None, "length not a multiple of 4 (NTPsec)"
    h = header_of(b, poll_unsigned=bool(R & {NS_POLL, NL_POLL}))
    if h.version not in (3, 4) and not R & {NS_VERSIONS, NL_VERSIONS, WS_VERSIONS}:
        return None, WHY_VERSION
    if not 1 <= h.mode <= 5 and not R & {NR_MODES, NS_MODES, NL_MODES, P_MODES}:
        if not (WS_MODE0 in R and h.mode == 0):
            return None, WHY_MODE
    if NL_TAIL in R:
        return ok(h, (), b""), None
    tail = b[48:]
    if WS_TAIL in R:
        return ws_tail(h, tail)
    if P_MACLEN in R and mac_length is not None:
        return pr3_tail(h, tail, mac_length, R)
    if h.version == 3 and not R & {NS_V3, P_V3}:
        if NR_V3 in R:
            return (ok(h, (), tail), None) if len(tail) == 0 or 4 <= len(tail) <= 24 else (None, WHY_V3)
        if len(tail) in (0, 20, 24) or tail == bytes(4) or (P_MAC4 in R and len(tail) == 4):
            return ok(h, (), tail), None
        return None, WHY_V3
    fields, i, n = [], 0, len(tail)
    while n - i > 24:
        if NS_FIELDS in R:
            size = be(tail[i + 4:i + 8])
            fields.append((be(tail[i:i + 4]), tail[i + 8:i + 8 + size]))
            i = min(n, i + 8 + size)
            continue
        t, size = be(tail[i:i + 2]), be(tail[i + 2:i + 4])
        if size < (4 if NR_MIN4 in R else 16):
            return None, WHY_SMALL
        if size % 4:
            return None, WHY_ALIGN
        if size > n - i:
            return None, WHY_PAST
        body = tail[i + 4:i + size]
        if NR_NTS in R and ((t == 0x0304 and any(body)) or (t == 0x0404 and not nts_fits(body))):
            return None, "an NTS field ntpd-rs refuses"
        fields.append((t, body))
        i += size
    left = tail[i:]
    if NS_TAIL in R:
        if len(left) in (4, 20, 24):
            return ok(h, fields, left), None
        if len(left) in (8, 12, 16):
            return None, "8, 12 or 16 octets left (NTPsec)"
        return ok(h, fields, b"", len(left)), None
    if NR_MAC in R:
        if len(left) == 0 or 4 <= len(left) <= 24:
            return ok(h, fields, left), None
        return None, why_left(left, fields)
    if len(left) in (0, 20, 24) or (left == bytes(4) and not fields) or (P_MAC4 in R and len(left) == 4):
        return ok(h, fields, left), None
    return None, why_left(left, fields)


def ws_tail(h, tail):
    """Wireshark 4.2.2, packet-ntp.c, dissect_ntp_std and dissect_ntp_ext."""
    n, end, last = len(tail), 0, 0
    while n - end >= 16:
        size = be(tail[end + 2:end + 4])
        if size < 16 or n - end < size:
            break
        end += size
        last = size
    left = n - end
    if left == 0 or (left == 4 and be(tail[end:end + 4]) == 0):
        pass
    elif left < 20:
        end -= last
    fields, i = [], 0
    while i < end:
        size = be(tail[i + 2:i + 4])
        if size < 8 or size % 4:
            return None, "a field Length Wireshark notes"
        fields.append((be(tail[i:i + 2]), tail[i + 4:i + size]))
        i += size
    if n - i >= 4:
        return ok(h, fields, tail[i:]), None
    return ok(h, fields, b"", n - i), None


def pr3_tail(h, tail, mac_length, R):
    """ntp#3's tests/wire_oracle.py `decode`: the MAC is the last
    mac_length octets, and every octet before it is in a field."""
    if mac_length not in (0, 4, 20, 24) or mac_length > len(tail):
        return None, "ntp#3: no room for the MAC"
    end = len(tail) - mac_length
    fields, i = [], 0
    while i < end:
        if end - i < 4:
            return None, WHY_LEFT_ODD
        t, size = be(tail[i:i + 2]), be(tail[i + 2:i + 4])
        if size < 16:
            return None, WHY_SMALL
        if size % 4:
            return None, WHY_ALIGN
        if size > end - i:
            return None, WHY_PAST
        fields.append((t, tail[i + 4:i + size]))
        i += size
    mac = tail[end:]
    if mac_length == 0 and fields and len(fields[-1][1]) + 4 < 28:
        return None, "ntp#3: a last field below 28 octets with no MAC"
    if h.version == 3 and fields and P_V3 not in R:
        return None, WHY_V3
    if P_MAC4 not in R and not mac_valid(fields, mac):
        return None, why_left(mac, fields)
    return ok(h, fields, mac), None


def to_unix(era, raw):
    """RFC 5905 section 6: the timestamp raw in era `era` is era * 2^32 +
    raw / 2^32 seconds from 0 h 1 January 1900; less 2,208,988,800
    seconds to 1970. Whole seconds and a fraction in units of 2^-32."""
    if raw == 0 or raw >= T64:
        return None
    t = era * T32 + Fraction(raw, T32) - UNIX_EPOCH
    s = math.floor(t)
    return s, int((t - s) * T32)


def from_unix(seconds, fraction):
    """RFC 5905 section 6: "era = s / 2^(32) and timestamp = s - era *
    2^(32)", s in seconds from 1900, the division rounding down."""
    if fraction >= T32:
        return None
    s = Fraction(seconds) + Fraction(fraction, T32) + UNIX_EPOCH
    era = math.floor(s / T32)
    raw = (s - era * T32) * T32
    assert raw.denominator == 1
    return None if raw == 0 else (era, int(raw))


# ---------------------------------------------------------------------
# Requests and answers, by the header of Main.lean.


def hexd(bs):
    return bs.hex() if bs else "-"


def show_fields(fields):
    return ",".join(f"{t}:{hexd(body)}" for t, body in fields) if fields else "-"


def show_packet(p):
    h, fields, mac = p[0], p[1], p[2]
    return " ".join([str(x) for x in h] + [show_fields(fields), hexd(mac)])


def show_answer(answer):
    return "FAIL" if answer is None else "OK " + show_packet(answer)


def model(op, args):
    """The model's answer to a request, and why it is FAIL (or None)."""
    if op == "decode":
        p = decode_spec(args[0])
        if p is None:
            return "FAIL", read(args[0])[1] or "the model's two readings differ"
        return "OK " + show_packet(p), None
    if op == "encode":
        p = args[0]
        return ("OK " + packet_bytes(p).hex(), None) if valid(p) else ("FAIL", "not Valid")
    if op == "unix":
        r = to_unix(*args)
        return ("FAIL", "no Unix time") if r is None else (f"OK {r[0]} {r[1]}", None)
    if op == "fromunix":
        r = from_unix(*args)
        return ("FAIL", "no timestamp") if r is None else (f"OK {r[0]} {r[1]}", None)
    raise ValueError(op)


def request(op, args):
    if op == "decode":
        return f"decode {hexd(args[0])}"
    if op == "encode":
        return "encode " + show_packet(args[0])
    return f"{op} {args[0]} {args[1]}"


DIGITS = frozenset("0123456789")
HEX_DIGITS = frozenset("0123456789abcdef")


def decimal(s):
    return int(s) if s and all(c in DIGITS for c in s) else None


def integer(s):
    if s.startswith("-"):
        n = decimal(s[1:])
        return None if n is None else -n
    return decimal(s)


def hex_field(f):
    if f == "-":
        return b""
    if not f or len(f) % 2 or any(c not in HEX_DIGITS for c in f):
        return None
    return bytes.fromhex(f)


def field_list(s):
    if s == "-":
        return ()
    out = []
    for f in s.split(","):
        parts = f.split(":")
        if len(parts) != 2:
            return None
        t, body = decimal(parts[0]), hex_field(parts[1])
        if t is None or body is None:
            return None
        out.append((t, body))
    return tuple(out)


def parse_request(line):
    """The operation and arguments of a request line, or None when it is
    malformed."""
    fs = line.split(" ")
    if fs[0] == "decode" and len(fs) == 2:
        b = hex_field(fs[1])
        return None if b is None else ("decode", [b])
    if fs[0] == "encode" and len(fs) == 16:
        nums = [integer(x) if k in (4, 5) else decimal(x) for k, x in enumerate(fs[1:14])]
        exts, mac = field_list(fs[14]), hex_field(fs[15])
        if any(x is None for x in nums) or exts is None or mac is None:
            return None
        return ("encode", [(Header(*nums), exts, mac)])
    if fs[0] == "unix" and len(fs) == 3:
        era, raw = integer(fs[1]), decimal(fs[2])
        return None if era is None or raw is None else ("unix", [era, raw])
    if fs[0] == "fromunix" and len(fs) == 3:
        s, f = integer(fs[1]), decimal(fs[2])
        return None if s is None or f is None else ("fromunix", [s, f])
    return None


def model_line(raw):
    """What the tool must answer to a request line, malformed or not."""
    line = raw[:-1] if raw.endswith("\n") else raw
    if raw.endswith("\n") and line.endswith("\r"):
        line = line[:-1]
    req = parse_request(line)
    return "error" if req is None else model(*req)[0]


def parse_decoded(text):
    """A `decode` answer of the tool's as (header, fields, MAC, 0), or
    None for FAIL."""
    if text == "FAIL":
        return None
    req = parse_request("encode " + text[3:]) if text.startswith("OK ") else None
    if req is None:
        raise ValueError(f"not a decode answer: {text[:100]}")
    h, exts, mac = req[1][0]
    return ok(h, exts, mac)


# ---------------------------------------------------------------------
# Ntp/Spec/Examples.lean, and Ntp/Spec.lean's `examples` and `rejects`.

CLIENT = bytes.fromhex("230206e8000003ff0000037d5ec69f0fe5f662987b61b9afe5f663667b64995d"
                       "e5f6636681405590e5f663a8761dde48")
SERVER = bytes.fromhex("240206e900000236000003b7c035676ce5f661fd6f165f03e5f663a87619ef40"
                       "e5f663a8798c6581e5f663a8798eae2b")
NTS_REPLY = bytes.fromhex(
    "240104e80000000000000060544d4e4ce8494892f929579e6287db473ff75f58e84948b2b640d701e84948b2b644bff8"
    "01040024e4833a8d600e1342435cb29de550acc0f8d8fa16e5c5370a620b155f586adad6040400d4001000bc6a1de3c2"
    "6e13eb10c739d70b841fad1b86e230c63e9ea5f71b62a8a79881ce7c6b17cb3132490fdecf2110564e368892ddeef1f4"
    "23f6555341c2c9176120a518dc1a7edc5ee3c83b05087b7303f7ab86d52cc7490ce829397223dcef2d94faf8d71d1280"
    "da032dd70469e9ac5f82ef5781d207fbacb4a8b6319114d5f56fb22a0cb6d7dcf77df02146f67e4601b53b217ca8ac1a"
    "4d97d59bceeb9833997f100ed469858bcd735201adec38cf8cb2c6d0541a9767ddb3ea091d63d98d03dd6e48153dc9b6"
    "1fe5d91d74ae3548")
FIELD16 = bytes([0x01, 0x04, 0x00, 0x10]) + bytes(range(0x11, 0x1D))
FIELD20 = bytes([0x02, 0x04, 0x00, 0x14]) + bytes(range(0x21, 0x31))
FIELD28 = bytes([0x01, 0x04, 0x00, 0x1C]) + bytes([0x5A] * 24)
MAC20 = bytes([0, 0, 0, 1]) + bytes(range(0xA0, 0xB0))
WITH_MAC = CLIENT + FIELD16 + FIELD20 + MAC20
CRYPTO_NAK = SERVER + bytes(4)
V3_WITH_MAC = bytes([0x1B]) + CLIENT[1:] + MAC20
TAIL24 = bytes([0x01, 0x04, 0x00, 0x18]) + bytes(range(0x31, 0x45))
# An Autokey ASSOC request field (RFC 5906 Figure 7 and 10.2) of 28
# octets whose Value Length, 0xFFFFFFFF, runs past it (CVE-2014-9750).
AUTOKEY_ASSOC = (bytes([0x01, 0x02, 0x00, 0x1C, 0, 0, 0, 1]) + bytes(8) + b"\xff\xff\xff\xff" + b"host"
                 + bytes(4))
# clientHeader, serverHeader and ntsHeader, as Ntp/Spec/Examples.lean gives
# them field by field.
CLIENT_HEADER = Header(0, 4, 3, 2, 6, -24, 0x000003FF, 0x0000037D, 0x5EC69F0F, 0xE5F662987B61B9AF,
                       0xE5F663667B64995D, 0xE5F6636681405590, 0xE5F663A8761DDE48)
SERVER_HEADER = Header(0, 4, 4, 2, 6, -23, 0x00000236, 0x000003B7, 0xC035676C, 0xE5F661FD6F165F03,
                       0xE5F663A87619EF40, 0xE5F663A8798C6581, 0xE5F663A8798EAE2B)
NTS_HEADER = Header(0, 4, 4, 1, 4, -24, 0, 0x00000060, 0x544D4E4C, 0xE8494892F929579E,
                    0x6287DB473FF75F58, 0xE84948B2B640D701, 0xE84948B2B644BFF8)


def stated(h, fields=(), mac=b""):
    """A `decode` answer, as Ntp/Spec.lean states it."""
    return "OK " + show_packet((h, fields, mac))


# What Ntp/Spec.lean states of an input it says only is accepted
# (`(Ntp.decode b).isSome`): any `OK` answer.
ACCEPTED = "OK, any packet"


def as_stated(answer, stated_answer):
    if stated_answer == ACCEPTED:
        return answer.startswith("OK ")
    return answer == stated_answer


SPEC_CASES = [
    # examples
    ("decode", [CLIENT], stated(CLIENT_HEADER)),
    ("decode", [SERVER], stated(SERVER_HEADER)),
    ("decode", [NTS_REPLY], stated(NTS_HEADER, ((0x0104, NTS_REPLY[52:84]), (0x0404, NTS_REPLY[88:])))),
    ("decode", [WITH_MAC], stated(CLIENT_HEADER, ((0x0104, FIELD16[4:]), (0x0204, FIELD20[4:])), MAC20)),
    ("decode", [CRYPTO_NAK], stated(SERVER_HEADER, (), bytes(4))),
    ("decode", [V3_WITH_MAC], stated(CLIENT_HEADER._replace(version=3), (), MAC20)),
    ("decode", [CLIENT + TAIL24], stated(CLIENT_HEADER, (), TAIL24)),
    ("decode", [CLIENT + AUTOKEY_ASSOC + MAC20], stated(CLIENT_HEADER, ((0x0102, AUTOKEY_ASSOC[4:]),), MAC20)),
    ("encode", [(SERVER_HEADER, (), b"")], f"OK {SERVER.hex()}"),
    ("unix", [0, 0xE5F663A8798EAE2B], f"OK 1649141032 {0x798EAE2B}"),
    ("fromunix", [1649141032, 0x798EAE2B], f"OK 0 {0xE5F663A8798EAE2B}"),
    ("unix", [0, 2208988800 * T32], "OK 0 0"),
    ("unix", [0, 0xFFFFFFFF00000000], "OK 2085978495 0"),
    ("unix", [0, 0x0000000100000000], "OK -2208988799 0"),
    ("unix", [1, 0x0000000100000000], "OK 2085978497 0"),
    ("unix", [1, 0], "FAIL"),
    ("fromunix", [2085978496, 0], "FAIL"),
    ("fromunix", [2085978496, 1], "OK 1 1"),
    ("unix", [-1, 0xFFFFFFFF00000000], "OK -2208988801 0"),
    # rejects: each refused packet after the accepted one it differs
    # from only in the rule it breaks (the server reply and the
    # crypto-NAK are above)
    ("decode", [bytes([0x14]) + SERVER[1:]], "FAIL"),
    ("decode", [bytes([0x2C]) + SERVER[1:]], "FAIL"),
    ("decode", [bytes([0x20]) + SERVER[1:]], "FAIL"),
    ("decode", [bytes([0x26]) + SERVER[1:]], "FAIL"),
    ("decode", [bytes([0x27]) + SERVER[1:]], "FAIL"),
    ("decode", [SERVER[:47]], "FAIL"),
    ("decode", [CLIENT + bytes([1, 4, 0, 0x10]) + bytes([0x5A] * 12) + FIELD28], ACCEPTED),
    ("decode", [CLIENT + bytes([1, 4, 0, 0x0C]) + bytes([0x5A] * 8) + FIELD28], "FAIL"),
    ("decode", [CLIENT + bytes([1, 4, 0, 0x20]) + bytes([0x5A] * 28)], ACCEPTED),
    ("decode", [CLIENT + bytes([1, 4, 0, 0x1E]) + bytes([0x5A] * 26)], "FAIL"),
    ("decode", [CLIENT + bytes([1, 4, 1, 0]) + bytes([0x5A] * 28)], "FAIL"),
    ("decode", [CLIENT + FIELD16 + FIELD28], ACCEPTED),
    ("decode", [CLIENT + FIELD28 + FIELD16], "FAIL"),
    ("decode", [SERVER + bytes([0, 0, 0, 1])], "FAIL"),
    ("decode", [SERVER + FIELD28], ACCEPTED),
    ("decode", [SERVER + FIELD28 + bytes(4)], "FAIL"),
    ("decode", [CLIENT + FIELD28], ACCEPTED),
    ("decode", [bytes([0x1B]) + CLIENT[1:] + FIELD28], "FAIL"),
    ("decode", [SERVER + MAC20], ACCEPTED),
    ("decode", [SERVER + MAC20 + bytes([0])], "FAIL"),
]

# ---------------------------------------------------------------------
# Building inputs.

NTS_TYPES = (0x0104, 0x0204, 0x0304, 0x0404)
OTHER_TYPES = (0x0000, 0xFFFF, 0x0002, 0x0102, 0x0201, 0x8002, 0xF5FF, 0xF501, 0xF503, 0xF504, 0x2005)
SPECIAL_32 = (0, 1, 0xFFFFFFFF, 0x80000000, 0x00010000)
SPECIAL_64 = (0, 1, T32, T32 - 1, T64 - 1, 1 << 63, UNIX_EPOCH << 32, 0xFFFFFFFF00000000)


def random_header(rng, version=None, mode=None):
    def n32():
        return rng.choice(SPECIAL_32) if rng.random() < 0.1 else rng.getrandbits(32)

    def n64():
        return rng.choice(SPECIAL_64) if rng.random() < 0.1 else rng.getrandbits(64)

    return Header(rng.randrange(4), version or rng.choice((4, 4, 4, 3)), mode or rng.randint(1, 5),
                  rng.randrange(256), rng.randrange(-128, 128), rng.randrange(-128, 128), n32(), n32(),
                  n32(), n64(), n64(), n64(), n64())


def field_length(rng, at_least=16):
    """A Length: mostly short, sometimes long, at times the largest."""
    r = rng.random()
    if r < 0.5:
        n = rng.choice((16, 20, 24, 28, 32, 36, 40, 44, 48))
    elif r < 0.85:
        n = 4 * rng.randint(4, 64)
    elif r < 0.97:
        n = 4 * rng.randint(4, 256)
    elif r < 0.995:
        n = 4 * rng.randint(4, 16383)
    else:
        n = 65532
    return max(n, at_least)


def random_body(rng, t, size):
    r = rng.random()
    if t == 0x0404 and r < 0.6 and size >= 4:
        # An NTS authenticator whose nonce and ciphertext fit (RFC 8915 5.6).
        nonce = rng.choice((0, 4, 12, 16, 16, 17))
        nonce = min(nonce, size - 4)
        room = size - 4 - (nonce + (-nonce) % 4)
        cipher = rng.randint(0, max(0, room)) if room >= 0 else 0
        return be_bytes(2, nonce) + be_bytes(2, cipher) + rng.randbytes(size - 4)
    if t == 0x0304 and r < 0.6:
        return bytes(size)
    if r < 0.2:
        return bytes(size)
    return rng.randbytes(size)


def random_type(rng):
    r = rng.random()
    if r < 0.3:
        return rng.choice(NTS_TYPES)
    if r < 0.4:
        return rng.choice(OTHER_TYPES)
    return rng.getrandbits(16)


def random_field(rng, at_least=16):
    t = random_type(rng)
    return (t, random_body(rng, t, field_length(rng, at_least) - 4))


def random_mac(rng, kind=None):
    kind = kind or rng.choice(("none", "none", "20", "24", "nak"))
    if kind == "20":
        return be_bytes(4, rng.choice((1, rng.getrandbits(32)))) + rng.randbytes(16)
    if kind == "24":
        return be_bytes(4, rng.choice((1, rng.getrandbits(32)))) + rng.randbytes(20)
    if kind == "nak":
        return bytes(4)
    return b""


def random_packet(rng, nfields=None, version=None):
    """A valid packet: a version 4 packet of 0 to 5 fields, or a
    version 3 one with none; no MAC, a MAC of 20 or 24 octets, or the
    crypto-NAK alone. At most 200000 octets, so tshark reads it."""
    h = random_header(rng, version=version or (4 if nfields else None))
    k = 0 if h.version == 3 else (rng.choice((0, 0, 1, 1, 2, 2, 3, 4, 5)) if nfields is None else nfields)
    while True:
        exts = [random_field(rng) for _ in range(k)]
        mac = random_mac(rng)
        if exts and mac == bytes(4):
            mac = b""
        if exts and not mac and ext_length(exts[-1]) < 28:
            t = exts[-1][0]
            exts[-1] = (t, random_body(rng, t, rng.choice((24, 28, 32, 60))))
        p = (h, tuple(exts), mac)
        if len(packet_bytes(p)) <= 200000:
            assert valid(p)
            return p


def field_raw(t, length, body):
    """A field's octets with any Length field, valid or not."""
    return be_bytes(2, t) + be_bytes(2, length) + body


# Autokey fields whose Value Length runs past the field: CVE-2014-9750
# came from following that length. The reader does not read it, so each
# such field must come back by its own Length, its octets unchanged.
AUTOKEY_LABEL = "an Autokey field whose Value Length runs past it (CVE-2014-9750)"


def autokey_field(code, response, length, value_length):
    """An Autokey field laid out as RFC 5906 Figure 7: the R and E bits
    and the Code, the Field Type (the Autokey version, 2), the Length,
    the Association ID, the Timestamp, the Filestamp, the Value Length,
    then length - 20 octets of Value and the rest."""
    return (bytes([0x80 * response + code, 2]) + be_bytes(2, length) + be_bytes(4, 0x1234)
            + bytes(4) + bytes(4) + be_bytes(4, value_length) + bytes(range(0x41, 0x41 + length - 20)))


def autokey_cases():
    """(octets, the answer Ntp.Spec.decode_iff fixes for them) for each
    Autokey case."""
    out = []
    for hb, h in ((CLIENT, CLIENT_HEADER), (SERVER, SERVER_HEADER)):
        for code in (1, 2, 3):
            for length in (28, 32, 64):
                for value_length in (length - 19, 0x10000, 0x80000000, 0xFFFFFFFF):
                    f = autokey_field(code, hb is SERVER, length, value_length)
                    e = (be(f[:2]), f[4:])
                    for pre, post, mac in (((), (), b""), ((), (), MAC20),
                                           (((0x0104, FIELD16[4:]),), (), MAC20 + b"\1\2\3\4"),
                                           ((), ((0x0104, FIELD28[4:]),), b"")):
                        fields = pre + (e,) + post
                        b = hb + b"".join(ext_bytes(x) for x in fields) + mac
                        out.append((b, stated(h, fields, mac)))
    return out


def broken_packet(rng):
    """A packet with one rule broken, built so that a reader without that
    rule could take it: (what was broken, octets)."""
    h = random_header(rng, version=4)
    hb = header_bytes(h)
    k = rng.randint(0, 3)
    before = b"".join(ext_bytes(random_field(rng)) for _ in range(k))
    mac = random_mac(rng, rng.choice(("none", "20", "24")))
    what = rng.choice((
        "a field of Length 0 to 12", "a field Length that is not a multiple of 4",
        "a field Length 4 past the end", "a field Length 1000 past the end",
        "a field Length of 65532 or 65535 past the end", "a last field of 16 to 24 octets with no MAC",
        "a MAC of 8, 12 or 16 octets", "a MAC of 21 to 23 octets", "a MAC of 28 or 32 octets",
        "four octets that are not zero", "a crypto-NAK after a field", "a field in version 3",
        "a version other than 3 and 4", "mode 0, 6 or 7", "an octet more at the end",
        "an octet less at the end", "a field Length 4 more or less"))
    t = random_type(rng)
    if what == "a field of Length 0 to 12":
        n = rng.choice((0, 4, 8, 12))
        bad = field_raw(t, n, rng.randbytes(max(0, n - 4)) if n else rng.randbytes(12))
        return what, hb + before + bad + ext_bytes(random_field(rng, 28)) + mac
    if what == "a field Length that is not a multiple of 4":
        n = rng.choice((17, 18, 19, 29, 30, 31, 4 * rng.randint(5, 40) + rng.randint(1, 3)))
        return what, hb + before + field_raw(t, n, rng.randbytes(n - 4)) + mac
    if what.startswith("a field Length") and "past the end" in what:
        rest_len = rng.choice((24, 28, 32, 60, 100))
        rest = rng.randbytes(rest_len - 4)
        if "4 past" in what:
            n = rest_len + 4
        elif "1000" in what:
            n = rest_len + 1000
        else:
            n = rng.choice((65532, 65535))
        return what, hb + before + field_raw(t, n, rest)
    if what == "a last field of 16 to 24 octets with no MAC":
        n = rng.choice((16, 20, 24))
        return what, hb + before + field_raw(t, n, rng.randbytes(n - 4))
    if what == "a MAC of 8, 12 or 16 octets":
        return what, hb + before + rng.randbytes(rng.choice((8, 12, 16)))
    if what == "a MAC of 21 to 23 octets":
        return what, hb + before + rng.randbytes(rng.choice((21, 22, 23)))
    if what == "a MAC of 28 or 32 octets":
        return what, hb + before + rng.randbytes(rng.choice((28, 32)))
    if what == "four octets that are not zero":
        return what, hb + be_bytes(4, rng.randint(1, T32 - 1))
    if what == "a crypto-NAK after a field":
        return what, hb + before + ext_bytes(random_field(rng)) + bytes(4)
    if what == "a field in version 3":
        h3 = header_bytes(h._replace(version=3))
        return what, h3 + ext_bytes(random_field(rng, 28)) + random_mac(rng, rng.choice(("none", "20")))
    if what == "a version other than 3 and 4":
        v = rng.choice((0, 1, 2, 5, 6, 7))
        return what, header_bytes(h._replace(version=v)) + before + mac
    if what == "mode 0, 6 or 7":
        m = rng.choice((0, 6, 7))
        return what, header_bytes(h._replace(mode=m)) + before + mac
    p = random_packet(rng)
    b = packet_bytes(p)
    if what == "an octet more at the end":
        return what, b + rng.randbytes(1)
    if what == "an octet less at the end":
        return what, b[:-1]
    # a field Length 4 more or less
    if not p[1]:
        p = random_packet(rng, nfields=rng.randint(1, 3))
        b = packet_bytes(p)
    j = rng.randrange(len(p[1]))
    at = 48 + sum(ext_length(e) for e in p[1][:j])
    n = ext_length(p[1][j]) + rng.choice((-4, 4))
    return what, b[:at + 2] + be_bytes(2, n % T16) + b[at + 4:]


def changed_packet(rng, b):
    """A valid packet changed at random: (how, octets)."""
    how = rng.choice(("an octet changed", "an octet of the tail changed", "a bit flipped",
                      "two or three octets changed", "an octet inserted", "an octet removed",
                      "a Length field changed"))
    b = bytearray(b)
    if how == "an octet changed":
        i = rng.randrange(len(b))
        b[i] = (b[i] + rng.randint(1, 255)) % 256
    elif how == "an octet of the tail changed" and len(b) > 48:
        i = rng.randrange(48, len(b))
        b[i] = (b[i] + rng.randint(1, 255)) % 256
    elif how == "a bit flipped":
        i = rng.randrange(len(b))
        b[i] ^= 1 << rng.randrange(8)
    elif how == "two or three octets changed":
        for i in rng.sample(range(len(b)), min(len(b), rng.randint(2, 3))):
            b[i] = (b[i] + rng.randint(1, 255)) % 256
    elif how == "an octet inserted":
        b.insert(rng.randint(0, len(b)), rng.randrange(256))
    elif how == "an octet removed":
        del b[rng.randrange(len(b))]
    elif how == "a Length field changed" and len(b) > 52:
        p = decode_spec(bytes(b))
        if p and p[1]:
            j = rng.randrange(len(p[1]))
            at = 48 + sum(ext_length(e) for e in p[1][:j])
            b[at + 2:at + 4] = be_bytes(2, rng.choice((rng.getrandbits(16), ext_length(p[1][j]) + 1,
                                                       ext_length(p[1][j]) - 1, 0, 0xFFFF)))
        else:
            b[48:52] = rng.randbytes(4)
    else:
        i = rng.randrange(len(b))
        b[i] = (b[i] + 1) % 256
        how = "an octet changed"
    return how, bytes(b)


# RFC 5905 Figure 4: (date, MJD, era, era offset), with errata 4025
# (the MJD of 1 Jan 0 is -678,941) and 6524 (the era offset of 1 Jan 1 is
# 202,934,144) applied: as printed, those two rows disagree with the rest
# of the table.
FIGURE_4 = [
    ("1 Jan -4712", -2400001, -49, 1795583104), ("1 Jan -1", -679306, -14, 139775744),
    ("1 Jan 0", -678941, -14, 171311744), ("1 Jan 1", -678575, -14, 202934144),
    ("4 Oct 1582", -100851, -3, 2873647488), ("15 Oct 1582", -100840, -3, 2874597888),
    ("31 Dec 1899", 15019, -1, 4294880896), ("1 Jan 1900", 15020, 0, 0),
    ("1 Jan 1970", 40587, 0, 2208988800), ("1 Jan 1972", 41317, 0, 2272060800),
    ("31 Dec 1999", 51543, 0, 3155587200), ("8 Feb 2036", 64731, 1, 63104),
]
ERRATA = {"1 Jan 0": ("MJD -678,491", "https://www.rfc-editor.org/errata/eid4025"),
          "1 Jan 1": ("era offset 202,939,144", "https://www.rfc-editor.org/errata/eid6524")}
UNIX_MJD = 40587  # the MJD of 1 Jan 1970


def time_inputs(rng, count):
    eras = (-1, 0, 1, 2)
    raws = (0, 1, T32 - 1, T32, T32 + 1, T64 - 1, UNIX_EPOCH << 32, 0xFFFFFFFF00000000,
            0xFFFFFFFFFFFFFFFF, 1 << 63, (1 << 63) - 1, 0x00000000FFFFFFFF, 0xE5F663A8798EAE2B)
    for e in eras:
        for r in raws:
            yield ("each of eras -1 to 2 with each special raw value", "unix", [e, r])
    for r in (T64, T64 + 1, 1 << 70, 10 ** 30):
        for e in (0, 1):
            yield ("a raw value of 2^64 or more", "unix", [e, r])
    # The end of era 0 in 2036 and the start of era 1.
    for k in range(-3, 4):
        for f in (0, 1, T32 - 1):
            yield ("the 2036 rollover", "unix", [0, ((T32 - 1 + k) % T32) * T32 + f])
            yield ("the 2036 rollover", "unix", [1, (k % T32) * T32 + f])
    for date, mjd, era, offset in FIGURE_4:
        yield ("a row of RFC 5905 Figure 4", "unix", [era, offset * T32])
        yield ("a row of RFC 5905 Figure 4", "fromunix", [(mjd - UNIX_MJD) * 86400, 0])
    for _ in range(count // 2):
        r = rng.random()
        era = rng.choice(eras) if r < 0.7 else rng.randint(-20, 20) if r < 0.9 else \
            rng.choice((-1, 1)) * rng.getrandbits(rng.choice((40, 70)))
        raw = rng.choice(raws) if rng.random() < 0.05 else rng.getrandbits(64)
        yield ("random", "unix", [era, raw])
    for k in range(-3, 4):
        s = k * T32 - UNIX_EPOCH
        for ds, f in ((0, 0), (0, 1), (-1, T32 - 1), (0, T32 - 1), (1, 0)):
            yield ("the first instant of an era, and around it", "fromunix", [s + ds, f])
    for _ in range(count // 2):
        r = rng.random()
        s = rng.randint(-(1 << 35), 1 << 35) if r < 0.8 else rng.choice((-1, 1)) * rng.getrandbits(70)
        f = rng.getrandbits(32) if rng.random() < 0.95 else T32 + rng.getrandbits(rng.choice((1, 40)))
        yield ("random", "fromunix", [s, f])


def every_value(label, b, positions):
    for i in positions:
        for v in range(256):
            if v != b[i]:
                yield (label, "decode", [b[:i] + bytes([v]) + b[i + 1:]])


def decode_inputs(rng, count):
    """Every `decode` input, labelled."""
    for op, args, _ in SPEC_CASES:
        if op == "decode":
            yield ("Ntp/Spec.lean's examples and rejects", op, args)
    shapes = [("the client request", CLIENT), ("the server reply", SERVER),
              ("the NTS reply", NTS_REPLY), ("the client request with two fields and a MAC", WITH_MAC),
              ("the crypto-NAK", CRYPTO_NAK), ("the version 3 packet with a MAC", V3_WITH_MAC),
              ("the client request with a 24-octet MAC", CLIENT + TAIL24),
              ("the client request with a 28-octet field", CLIENT + FIELD28)]
    for name, b in shapes:
        yield from every_value(f"every value of the first octet, in {name}", b, [0])
    yield from every_value("every value of every header octet, in the server reply", SERVER, range(48))
    for _ in range(count // 5):
        if rng.random() < 0.2:
            yield ("random octets, 48 of them", "decode", [rng.randbytes(48)])
        else:
            yield ("a header from random fields", "decode", [header_bytes(random_header(rng))])
    for _ in range(count):
        p = random_packet(rng)
        yield (f"a random packet, {len(p[1])} fields", "decode", [packet_bytes(p)])
    for _ in range(count // 5):
        what, b = broken_packet(rng)
        yield ("a random packet, " + what, "decode", [b])
    # Tails of every length after a version 4 and a version 3 header.
    v3 = bytes([0x1B]) + CLIENT[1:]
    for name, hb in (("version 4", CLIENT), ("version 3", v3)):
        for n in range(81):
            yield (f"a tail of every length from 0 to 80, {name}, zeros", "decode", [hb + bytes(n)])
            yield (f"a tail of every length from 0 to 80, {name}, random", "decode", [hb + rng.randbytes(n)])
            yield (f"a tail of every length from 0 to 80, {name}, all ones", "decode", [hb + b"\xff" * n])
            if n >= 4:
                yield (f"a tail of every length from 0 to 80, {name}, one field of that length", "decode",
                       [hb + field_raw(random_type(rng), n, rng.randbytes(n - 4))])
    for n in range(81):
        body = rng.randbytes(max(0, n - 4)) if n >= 4 else b""
        f = field_raw(0x0104, n, body)
        yield ("a field of every Length from 0 to 80", "decode", [CLIENT + f])
        yield ("a field of every Length from 0 to 80, then a 20-octet MAC", "decode", [CLIENT + f + MAC20])
        yield ("a field of every Length from 0 to 80, after a field of 28", "decode", [CLIENT + FIELD28 + f])
    # Version 3, each kind of tail.
    for name, tail in (("none", b""), ("a crypto-NAK", bytes(4)), ("four octets that are not zero", b"\0\0\0\7"),
                       ("a 20-octet MAC", MAC20), ("a 24-octet MAC", MAC20 + b"\1\2\3\4"),
                       ("21 to 23 octets", MAC20 + b"\1"), ("21 to 23 octets", MAC20 + b"\1\2"),
                       ("21 to 23 octets", MAC20 + b"\1\2\3"), ("8, 12 or 16 octets", MAC20[:8]),
                       ("8, 12 or 16 octets", MAC20[:12]), ("8, 12 or 16 octets", MAC20[:16]),
                       ("a field of 28 octets", FIELD28), ("a field of 28 octets and a MAC", FIELD28 + MAC20),
                       ("a field of 16 octets and a MAC", FIELD16 + MAC20), ("a 72-octet MS-SNTP tail",
                                                                             b"\0\0\0\1" + bytes(68))):
        yield (f"version 3 with {name}", "decode", [v3 + tail])
    # MACs and crypto-NAKs after the header and after fields.
    for pre_name, pre in (("after the header", b""), ("after a field of 16", FIELD16),
                          ("after a field of 28", FIELD28)):
        for n in (4, 20, 21, 22, 23, 24):
            for content in ("zeros", "random"):
                tail = bytes(n) if content == "zeros" else rng.randbytes(n)
                yield (f"a MAC of 4 or 20 to 24 octets, {pre_name}", "decode", [SERVER + pre + tail])
    # Lengths that run past the end: by 4, by 1000, at each position.
    for pos in range(3):
        for over in (4, 1000, None):
            for left in (24, 28, 32, 64):
                before = b"".join(ext_bytes(random_field(rng)) for _ in range(pos))
                n = left + over if over else 65532
                yield ("a field Length running 4 or 1000 octets past the end, or to 65532", "decode",
                       [CLIENT + before + field_raw(0x0104, n, rng.randbytes(left - 4))])
    for b, _ in autokey_cases():
        yield (AUTOKEY_LABEL, "decode", [b])
    # Truncations of valid packets at every length.
    for name, b in shapes:
        for n in range(len(b)):
            yield ("a packet cut short, at every length", "decode", [b[:n]])
    for _ in range(max(1, count // 100)):
        p = random_packet(rng, nfields=rng.randint(0, 3))
        b = packet_bytes(p)
        cuts = range(len(b)) if len(b) <= 400 else sorted(set(rng.sample(range(len(b)), 200)) | {47, 48})
        for n in cuts:
            yield ("a random packet cut short, at every length", "decode", [b[:n]])
    # Random changes of valid packets.
    for _ in range(count // 5):
        how, b = changed_packet(rng, packet_bytes(random_packet(rng)))
        yield ("a random packet, " + how, "decode", [b])
    # Two of the largest fields, and one field of every size class.
    for n in (65532, 65528):
        t = rng.getrandbits(16)
        yield ("the largest fields", "decode", [CLIENT + field_raw(t, n, rng.randbytes(n - 4))])
        yield ("the largest fields", "decode", [CLIENT + field_raw(t, n, rng.randbytes(n - 4)) + MAC20])
    yield ("the largest fields", "decode", [CLIENT + field_raw(1, 65532, bytes(65528)) + FIELD16 + MAC20])
    for _, b, _, _ in vector_answers():
        yield ("a vector of pull request 3", "decode", [b])


def bad_encodes(rng):
    """Packets that are not valid, each in one way, to `encode`."""
    h = SERVER_HEADER
    for what, p in (
            ("a leap indicator of 4", (h._replace(leap=4), (), b"")),
            ("version 2", (h._replace(version=2), (), b"")), ("version 5", (h._replace(version=5), (), b"")),
            ("version 8", (h._replace(version=8), (), b"")),
            ("mode 0", (h._replace(mode=0), (), b"")), ("mode 6", (h._replace(mode=6), (), b"")),
            ("mode 7", (h._replace(mode=7), (), b"")), ("mode 8", (h._replace(mode=8), (), b"")),
            ("stratum 256", (h._replace(stratum=256), (), b"")),
            ("poll 128", (h._replace(poll=128), (), b"")), ("poll -129", (h._replace(poll=-129), (), b"")),
            ("precision 128", (h._replace(precision=128), (), b"")),
            ("precision -129", (h._replace(precision=-129), (), b"")),
            ("root delay 2^32", (h._replace(root_delay=T32), (), b"")),
            ("root dispersion 2^32", (h._replace(root_dispersion=T32), (), b"")),
            ("reference ID 2^32", (h._replace(ref_id=T32), (), b"")),
            ("reference timestamp 2^64", (h._replace(reference=T64), (), b"")),
            ("origin timestamp 2^64", (h._replace(origin=T64), (), b"")),
            ("receive timestamp 2^64", (h._replace(receive=T64), (), b"")),
            ("transmit timestamp 2^64", (h._replace(transmit=T64), (), b"")),
            ("a field type of 2^16", (h, ((T16, FIELD28[4:]),), b"")),
            ("a field body of 13 octets", (h, ((1, bytes(13)), (2, bytes(24))), b"")),
            ("a field body of 25 octets", (h, ((1, bytes(25)),), b"")),
            ("a field body of 8 octets", (h, ((1, bytes(8)), (2, bytes(24))), b"")),
            ("a field body of none", (h, ((1, b""), (2, bytes(24))), b"")),
            ("a field body of 65532 octets", (h, ((1, bytes(65532)),), b"")),
            ("a last field of 16 octets with no MAC", (h, ((1, bytes(24)), (2, bytes(12))), b"")),
            ("a last field of 24 octets with no MAC", (h, ((1, bytes(20)),), b"")),
            ("a MAC of 21 octets", (h, (), bytes(21))), ("a MAC of 16 octets", (h, (), bytes(16))),
            ("a MAC of 28 octets", (h, (), bytes(28))),
            ("four octets that are not zero", (h, (), b"\0\0\0\1")),
            ("a crypto-NAK after a field", (h, ((1, bytes(12)),), bytes(4))),
            ("a field in version 3", (h._replace(version=3), ((1, bytes(24)),), b"")),
            ("a field in version 3, and a MAC", (h._replace(version=3), ((1, bytes(12)),), MAC20)),
    ):
        yield ("a packet not valid in one way, encoded: " + what, "encode", [p])
    for _ in range(50):
        p = random_packet(rng)
        what = rng.choice(("a leap indicator of 4 to 7", "version 2 or 5", "a field body not a whole word",
                           "a MAC of 21 octets"))
        h, exts, mac = p
        if what == "a leap indicator of 4 to 7":
            p = (h._replace(leap=rng.randint(4, 7)), exts, mac)
        elif what == "version 2 or 5":
            p = (h._replace(version=rng.choice((2, 5))), exts, mac)
        elif what == "a field body not a whole word":
            p = (h, exts + ((1, bytes(rng.choice((25, 26, 27)))),), mac)
        else:
            p = (h, exts, bytes(21))
        yield ("a random packet not valid in one way, encoded", "encode", [p])


def inputs(seed, count):
    """Every request but the malformed ones, labelled: (label, op, args)."""
    rng = random.Random(seed)
    items = list(decode_inputs(rng, count))
    out = list(items)
    for op, args, _ in SPEC_CASES:
        if op != "decode":
            out.append(("Ntp/Spec.lean's examples and rejects", op, args))
    # `encode` of every packet the model reads.
    for label, op, args in items:
        p = decode_spec(args[0])
        if p is not None:
            out.append(("a packet the model reads, encoded", "encode", [p]))
    out += list(bad_encodes(rng))
    times = list(time_inputs(rng, count))
    out += times
    # `fromunix` of every Unix time `unix` gives.
    for label, op, args in times:
        if op == "unix":
            r = to_unix(*args)
            if r is not None:
                out.append(("the Unix time of a `unix` request, back", "fromunix", list(r)))
    return out

# ---------------------------------------------------------------------
# Running a program over request lines.


def run_lines(cmd, lines, timeout=TIMEOUT, cwd=None, env=None):
    """Send `lines` to `cmd` and return its answer lines and a note on
    how the run failed, or None."""
    raw = "".join(lines).encode("utf-8")
    proc = subprocess.Popen(cmd, stdin=subprocess.PIPE, stdout=subprocess.PIPE,
                            stderr=subprocess.PIPE, cwd=cwd, env=env)
    out, err = bytearray(), bytearray()

    def feed():
        try:
            proc.stdin.write(raw)
            proc.stdin.close()
        except (BrokenPipeError, ValueError):
            pass

    def drain(stream, buf):
        while chunk := stream.read1(1 << 16):
            buf += chunk

    threads = [threading.Thread(target=feed),
               threading.Thread(target=drain, args=(proc.stdout, out)),
               threading.Thread(target=drain, args=(proc.stderr, err))]
    for t in threads:
        t.start()
    problem = None
    try:
        proc.wait(timeout=timeout)
    except subprocess.TimeoutExpired:
        proc.kill()
        problem = f"no end after {timeout} seconds"
    for t in threads:
        t.join()
    proc.wait()
    if proc.returncode != 0 and not problem:
        tail = " / ".join(err.decode("utf-8", "backslashreplace").splitlines()[-3:])
        problem = f"exit status {proc.returncode}: {tail}"
    text = bytes(out).decode("utf-8", "backslashreplace")
    if text and not text.endswith("\n"):
        problem = problem or "the last answer has no LF"
    answers = text.split("\n")
    if answers and answers[-1] == "":
        answers.pop()
    return answers, problem


def run_parallel(cmd, lines, jobs):
    """`run_lines` over `jobs` processes, each given a run of the lines
    in order; the answers in order, and the problems."""
    size = -(-len(lines) // jobs) if lines else 0
    chunks = [lines[k:k + size] for k in range(0, len(lines), size)] if size else [[]]
    results = [None] * len(chunks)

    def one(k):
        results[k] = run_lines(cmd, chunks[k])

    threads = [threading.Thread(target=one, args=(k,)) for k in range(len(chunks))]
    for t in threads:
        t.start()
    for t in threads:
        t.join()
    answers, problems = [], []
    for chunk, (got, problem) in zip(chunks, results):
        if problem:
            problems.append(problem)
        if len(got) != len(chunk):
            problems.append(f"{len(got)} answers for {len(chunk)} requests")
            got = (got + [""] * len(chunk))[:len(chunk)]
        answers += got
    return answers, problems


def first_line(cmd):
    try:
        out = subprocess.run(cmd, capture_output=True, text=True, timeout=300)
        return (out.stdout or out.stderr).strip().splitlines()[0]
    except (OSError, subprocess.SubprocessError, IndexError):
        return "unknown"


# ---------------------------------------------------------------------
# The oracles. Each gives, for a list of packets, its answers in one
# form: None when it refuses the packet, else (header, fields, MAC,
# octets shown nowhere), with what it does not give as None.


def setup_ntpdrs(tmp):
    """Build tests/ntpd-rs; its copy in tmp and a description, or None
    and why it is left out."""
    lock = (NTPDRS_SOURCE / "Cargo.lock").read_text(encoding="utf-8")
    m = re.search(r'name = "ntp-proto"\nversion = "([^"]+)"', lock)
    if not m or m.group(1) != NTP_PROTO_PINNED:
        return None, f"Cargo.lock does not pin ntp-proto {NTP_PROTO_PINNED}"
    if not shutil.which("cargo"):
        return None, "cargo is not installed"
    env = dict(os.environ, CARGO_TARGET_DIR=str(NTPDRS_TARGET))
    try:
        build = subprocess.run(["cargo", "build", "--release", "--locked", "--quiet"], cwd=NTPDRS_SOURCE,
                               env=env, capture_output=True, text=True, errors="backslashreplace",
                               timeout=TIMEOUT)
    except (OSError, subprocess.SubprocessError) as e:
        return None, f"`cargo build` failed: {e}"
    if build.returncode != 0:
        last = (build.stderr.strip().splitlines() or ["no output"])[-1]
        return None, f"`cargo build --release --locked` failed: {last[:200]}"
    exe = tmp / "ntpdrs-oracle"
    shutil.copy2(NTPDRS_TARGET / "release" / "ntpdrs-oracle", exe)
    return exe, (f"ntpd-rs: the ntp-proto crate {m.group(1)}, `NtpPacket::deserialize`, through "
                 f"tests/ntpd-rs (every crate pinned by its Cargo.lock), built with "
                 f"{first_line(['rustc', '--version'])}")


def ntpdrs_answers(exe, packets):
    """The answers of tests/ntpd-rs: OK, the version, the leap indicator
    and 11 more header fields, the fields, the MAC and one more column;
    or FAIL."""
    lines = [hexd(b) + "\n" for b in packets]
    out, problems = run_parallel([str(exe)], lines, JOBS)
    answers = []
    for line in out:
        if line.startswith("FAIL"):
            answers.append(None)
            continue
        fs = line.split(" ")
        if fs[0] != "OK" or len(fs) != 17:
            answers.append(("unreadable", line[:200]))
            continue
        nums = [int(x) for x in fs[1:14]]
        nums[0], nums[1] = nums[1], nums[0]
        fields = ()
        if fs[14] != "-":
            fields = tuple((int(t), None if body == "*" else (b"" if body == "-" else bytes.fromhex(body)))
                           for t, body in (f.split(":") for f in fs[14].split(",")))
        answers.append((Header(*nums), fields, b"" if fs[15] == "-" else bytes.fromhex(fs[15]), 0))
    return answers, problems


def setup_ntpsec():
    try:
        import ntp.packet
        import ntp.poly
    except ImportError as e:
        return None, f"the Python module of NTPsec is not installed ({e})"
    version = first_line(["dpkg-query", "-W", "-f", "${Version}\n", "python3-ntp"])
    if not version.startswith(NTPSEC_PINNED + "+") and version != NTPSEC_PINNED:
        return None, f"python3-ntp {version} is installed, not {NTPSEC_PINNED}"
    return ntp, (f"NTPsec: `ntp.packet.SyncPacket.analyze` of python3-ntp {version} (NTPsec "
                 f"{NTPSEC_PINNED}), from {Path(ntp.packet.__file__).parent}")


def ntpsec_answers(ntp, packets):
    answers = []
    for b in packets:
        p = ntp.packet.SyncPacket()
        try:
            p.analyze(ntp.poly.polybytes(b))
        except ntp.packet.SyncException:
            answers.append(None)
            continue
        h = Header(p.li_vn_mode >> 6, p.version(), p.mode(), p.stratum, p.poll, p.precision,
                   p.root_delay, p.root_dispersion, p.refid, p.reference_timestamp, p.origin_timestamp,
                   p.receive_timestamp, p.transmit_timestamp)
        mac = bytes(p.mac) if isinstance(p.mac, (bytes, bytearray)) else b""
        answers.append((h, tuple((t, bytes(d)) for t, d in p.extfields), mac, None))
    return answers, []


def setup_ntplib():
    try:
        import ntplib
    except ImportError as e:
        return None, f"ntplib is not installed ({e})"
    try:
        from importlib.metadata import version
        v = version("ntplib")
    except Exception:  # no metadata
        v = "unknown"
    if v != NTPLIB_PINNED:
        return None, f"ntplib {v} is installed, not {NTPLIB_PINNED}"
    return ntplib, f"ntplib {v}: `NTPPacket.from_data`, for the header fields only"


def ntplib_time(raw):
    """ntplib's _to_time: a 64-bit timestamp as a float."""
    return (raw >> 32) + float(raw & 0xFFFFFFFF) / 2 ** 32


def ntplib_view(a):
    """The header as ntplib keeps it."""
    if a is None:
        return None
    h = a[0]
    return (h.leap, h.version, h.mode, h.stratum, h.poll, h.precision, float(h.root_delay) / 2 ** 16,
            float(h.root_dispersion) / 2 ** 16, h.ref_id, ntplib_time(h.reference), ntplib_time(h.origin),
            ntplib_time(h.receive), ntplib_time(h.transmit))


def ntplib_answers(ntplib, packets):
    answers = []
    for b in packets:
        p = ntplib.NTPPacket()
        try:
            p.from_data(b)
        except ntplib.NTPException:
            answers.append(None)
            continue
        answers.append((p.leap, p.version, p.mode, p.stratum, p.poll, p.precision, p.root_delay,
                        p.root_dispersion, p.ref_id, p.ref_timestamp, p.orig_timestamp, p.recv_timestamp,
                        p.tx_timestamp))
    return answers, []


def setup_tshark():
    if not shutil.which("tshark"):
        return None, "tshark is not installed"
    line = first_line(["tshark", "--version"])
    m = re.search(r"TShark \(Wireshark\) (\S+)", line)
    if not m or m.group(1) != TSHARK_PINNED:
        return None, f"{line} is installed, not Wireshark {TSHARK_PINNED}"
    return "tshark", f"Wireshark: the NTP dissector of {line.rstrip('.')}, through `tshark -T pdml`"


PDML_ATTR = re.compile(r'(\w+)="([^"]*)"')


def tshark_answers(tmp, packets):
    """Write the packets as a capture of link type 147 (user 0), have
    tshark read it with the NTP dissector registered for that link type,
    and read its PDML."""
    path = tmp / "packets.pcap"
    sent = [i for i, b in enumerate(packets) if len(b) <= TSHARK_MAX]
    with open(path, "wb") as f:
        f.write(struct.pack("<IHHiIII", 0xA1B2C3D4, 2, 4, 0, 0, TSHARK_MAX, 147))
        for k, i in enumerate(sent):
            b = packets[i]
            f.write(struct.pack("<IIII", k, 0, len(b), len(b)))
            f.write(b)
    proc = subprocess.Popen(["tshark", "-n", "-o", 'uat:user_dlts:"User 0 (DLT=147)","ntp","0","","0",""',
                             "-r", str(path), "-T", "pdml"], stdout=subprocess.PIPE,
                            stderr=subprocess.DEVNULL, text=True, errors="backslashreplace")
    found = []
    state = None
    for line in proc.stdout:
        s = line.strip()
        if s == "<packet>":
            state = {"proto": None, "flagged": False, "f": {}, "exts": [], "mac": b""}
            continue
        if state is None:
            continue
        if s == "</packet>":
            found.append(state)
            state = None
            continue
        if s.startswith("<proto "):
            name = PDML_ATTR.search(s).group(2)
            state["proto"] = name
            if name == "_ws.malformed":
                state["flagged"] = True
            continue
        if not s.startswith("<field "):
            continue
        a = dict(PDML_ATTR.findall(s))
        name = a.get("name", "")
        if name.startswith("_ws.expert") and state["proto"] == "ntp":
            state["flagged"] = True
        elif name == "ntp.ext":
            state["exts"].append([None, b""])
        elif name == "ntp.ext.type":
            state["exts"][-1][0] = int(a["value"], 16)
        elif name == "ntp.ext.value":
            state["exts"][-1][1] = bytes.fromhex(a["value"])
        elif name in ("ntp.keyid", "ntp.mac"):
            state["mac"] += bytes.fromhex(a["value"])
        elif name in ("ntp.flags.li", "ntp.flags.vn", "ntp.flags.mode", "ntp.ppoll", "ntp.precision"):
            state["f"][name] = int(a["show"])
        elif name in ("ntp.stratum", "ntp.rootdelay", "ntp.rootdispersion", "ntp.refid", "ntp.reftime",
                      "ntp.org", "ntp.rec", "ntp.xmt"):
            state["f"][name] = int(a["value"], 16)
    proc.wait()
    problems = [] if proc.returncode == 0 else [f"tshark exited {proc.returncode}"]
    if len(found) != len(sent):
        problems.append(f"tshark gave {len(found)} packets for {len(sent)}")
    answers = ["not read: longer than tshark's largest frame"] * len(packets)
    keys = ("ntp.flags.li", "ntp.flags.vn", "ntp.flags.mode", "ntp.stratum", "ntp.ppoll", "ntp.precision",
            "ntp.rootdelay", "ntp.rootdispersion", "ntp.refid", "ntp.reftime", "ntp.org", "ntp.rec",
            "ntp.xmt")
    for i, st in zip(sent, found):
        f = st["f"]
        if st["flagged"] or f.get("ntp.flags.mode") in (6, 7):
            answers[i] = None
            continue
        if any(k not in f for k in keys):
            answers[i] = ("unreadable", "header fields missing")
            continue
        fields = tuple((t, body) for t, body in st["exts"])
        shown = 48 + sum(4 + len(body) for _, body in fields) + len(st["mac"])
        answers[i] = (Header(*(f[k] for k in keys)), fields, st["mac"], len(packets[i]) - shown)
    return answers, problems


def explain(b, oracle, want, view, mac_length=None):
    """The smallest set of the oracle's switches with which the model
    gives its answer, or None. The empty set means the model alone gives
    it."""
    rules = [r for r in ORACLE_RULES[oracle] if relevant(r, b)]
    for k in range(len(rules) + 1):
        for s in itertools.combinations(rules, k):
            if view(read(b, frozenset(s), mac_length)[0]) == want:
                return s
    return None


VIEWS = {
    "ntpd-rs": lambda a: None if a is None else (a[0], tuple((t, None if t == 0x0404 else body)
                                                             for t, body in a[1]), a[2], 0),
    "NTPsec": lambda a: None if a is None else (a[0], a[1], a[2], None),
    "Wireshark": lambda a: a,
    "ntplib": ntplib_view,
    "ntp#3": lambda a: None if a is None else (a[0], a[1], a[2], None),
}


def short(text, n=200):
    text = str(text)
    return text if len(text) <= n else text[:n] + f"... ({len(text)} characters)"


def show_any(a):
    """An answer of an oracle's, for the record."""
    if a is None:
        return "refused"
    if isinstance(a, tuple) and len(a) == 4 and isinstance(a[0], Header):
        h, fields, mac, rest = a
        text = " ".join(str(x) for x in h) + " fields " + (
            ",".join(f"{t}:{'?' if body is None else hexd(body)}" for t, body in fields) or "-") + \
            f" MAC {hexd(mac)}"
        return text + (f", {rest} octets shown nowhere" if rest else "")
    return str(a)


def show_tail(a, other):
    """An answer, without its header unless the other answer has
    another one."""
    if a is not None and (other is None or a[0] == other[0]):
        return show_any(a).split(" fields ", 1)[1].join(("fields ", ""))
    return show_any(a)


def tags(oracle, rules):
    """The numbers of the oracle's choices, as the record lists them."""
    nums = [str(ORACLE_RULES[oracle].index(r) + 1) for r in rules]
    if not nums:
        return "no choice"
    return ("choice " if len(nums) == 1 else "choices ") + ", ".join(nums[:-1]) + \
        (" and " if len(nums) > 1 else "") + nums[-1]


class Comparison:
    """An oracle's answers against the tool's, with the model's
    reasons."""

    def __init__(self, name):
        self.name = name
        self.asked = 0
        self.agree = 0
        self.asked_read = 0
        self.agree_read = 0
        self.model_right = 0
        self.named = collections.OrderedDict()
        self.failures = []

    def add(self, b, tool, want, mac_length=None, label=None):
        view = VIEWS[self.name]
        self.asked += 1
        full = view(read(b, frozenset(ORACLE_RULES[self.name]), mac_length)[0])
        where = label or f"decode {short(hexd(b), 120)}"
        if full == want:
            self.model_right += 1
        else:
            self.failures.append((f"{self.name}, the model with its rules: {where}", short(show_any(want), 300),
                                  short(show_any(full), 300)))
        got = view(tool)
        reads = tool is not None
        self.asked_read += reads
        if got == want:
            self.agree += 1
            self.agree_read += reads
            return
        rules = explain(b, self.name, want, view, mac_length)
        if not rules:
            self.failures.append((f"{self.name}: {where}", short(show_any(want), 300), short(show_any(got), 300)))
            return
        n, example = self.named.get(rules, (0, None))
        if example is None:
            example = f"{short(where, 110)}: the tool {short(show_any(got), 150)}; {self.name} " \
                      f"{short(show_any(want), 150)}"
        self.named[rules] = (n + 1, example)

# ---------------------------------------------------------------------
# Malformed and odd requests, and the command line.

SERVER_FIELDS = show_packet((SERVER_HEADER, (), b"")).split(" ")


def encode_with(k, value):
    fs = list(SERVER_FIELDS)
    fs[k] = value
    return "encode " + " ".join(fs)


MALFORMED = [
    "", " ", "\t", "decode", "decode 0", "decode 0A", "decode 00 00", "decode zz", "decode  00", " decode 00",
    "DECODE 00", "Decode 00", "decode\t00", "decode --", "decode +00", "decode 0x00", "decode é0", "decode ",
    "decode -0", "decode 0-", "decode00", "decode FF", "decode Ff", "decode fF", "decode 00\rx",
    "encode", "encode -", "encode " + " ".join(SERVER_FIELDS[:14]), "encode " + " ".join(SERVER_FIELDS + ["-"]),
    "encode  " + " ".join(SERVER_FIELDS), "encode " + " ".join(SERVER_FIELDS) + " ",
    encode_with(0, "-0"), encode_with(0, "+0"), encode_with(0, "0x0"), encode_with(0, ""),
    encode_with(1, "4.0"), encode_with(3, "-1"), encode_with(4, "--6"), encode_with(4, "+6"),
    encode_with(4, "-"), encode_with(4, "6-"), encode_with(5, ""), encode_with(6, "1e3"),
    encode_with(8, "٣"), encode_with(9, "0x1"), encode_with(12, "1_000"),
    encode_with(13, "260"), encode_with(13, "260:"), encode_with(13, ":00"), encode_with(13, "260:00:00"),
    encode_with(13, "x:00"), encode_with(13, "260:0"), encode_with(13, "260:zz"), encode_with(13, "260:00,"),
    encode_with(13, ",260:00"), encode_with(13, "-1:00"), encode_with(13, "260:-0"), encode_with(13, "260:AB"),
    encode_with(13, ""), encode_with(14, ""), encode_with(14, "0"), encode_with(14, "zz"), encode_with(14, "-0"),
    "unix", "unix 0", "unix 0 0 0", "unix +0 1", "unix 0 -1", "unix 0 1.5", "unix x 1", "unix 0 ０",
    "unix - 1", "unix -- 1", "unix 0 +1", "unix 1e3 1", "unix  0 1", "unix 0  1", "unix 0 1 ", "unix 0 0x1",
    "fromunix", "fromunix 0", "fromunix 0 -1", "fromunix 0 1 2", "fromunix 1e3 0", "fromunix 0 0x1",
    "fromunix - 0", "fromunix -+1 0", "serve", "unix0 1", "fromunix0 0", "UNIX 0 1", "FromUnix 0 0",
]
ODD = ["decode -", "unix -0 1", "unix 00 01", "unix 0 99999999999999999999999", "unix 99999999999999999999 1",
       "unix -99999999999999999999 1", "fromunix 0 4294967296", "fromunix -0 0",
       "fromunix 99999999999999999999999 0", "fromunix 0 0", "fromunix -2208988800 0",
       "encode " + " ".join("000" + f if f[0].isdigit() else f for f in SERVER_FIELDS),
       encode_with(4, "-0"), encode_with(13, "00260:" + FIELD28[4:].hex()), encode_with(3, "99999999999999999999"),
       encode_with(13, "260:-"), encode_with(13, "65536:" + FIELD28[4:].hex())]
# Last lines with no LF, with CR LF, with a lone CR: (request, answer).
AT_EOF = [("decode -", "FAIL"), ("unix 0 1\r\n", model_line("unix 0 1\n")),
          ("fromunix 0 0", model_line("fromunix 0 0\n")), ("decode -\r", "error")]


def cli_cases():
    """Runs of the command line: (arguments, standard input, the lines
    the run must print on standard output, its exit status), from the
    header of Main.lean: `ntp serve` and nothing else."""
    cases = [(["serve"], b"", [], 0),
             (["serve"], b"unix 0 1\ndecode -\n", [model_line("unix 0 1\n"), "FAIL"], 0)]
    for args in ([], ["serve", "x"], ["decode", "00"], ["Serve"], ["--help"], [""], ["serve", ""], ["dump"]):
        cases.append((args, b"", [], 2))
    return cases


def run_cli(cases):
    right, failures = 0, []
    for args, stdin, want, status in cases:
        try:
            p = subprocess.run([str(EXE)] + args, input=stdin, capture_output=True, timeout=600)
            text = p.stdout.decode("utf-8", "backslashreplace")
            got, code_ = (text[:-1].split("\n") if text.endswith("\n") else ([text] if text else [])), p.returncode
        except (OSError, subprocess.SubprocessError) as e:
            got, code_ = [str(e)], None
        if (got, code_) == (want, status):
            right += 1
        else:
            failures.append((f"ntp {' '.join(args)}"[:120], f"{want}, exit {status}", f"{got[:3]}, exit {code_}"))
    return right, failures


# ---------------------------------------------------------------------
# Unix time against RFC 5905 Figure 4 and Python's datetime.

EPOCH_1900 = datetime.datetime(1900, 1, 1, tzinfo=datetime.timezone.utc)
EPOCH_1970 = datetime.datetime(1970, 1, 1, tzinfo=datetime.timezone.utc)


def datetime_unix(era, raw):
    """The Unix time of the timestamp, by Python's datetime: 1900-01-01
    plus era * 2^32 + raw / 2^32 seconds; None outside its years."""
    try:
        d = EPOCH_1900 + datetime.timedelta(seconds=era * T32 + (raw >> 32))
    except (OverflowError, ValueError):
        return None
    return (d - EPOCH_1970) // datetime.timedelta(seconds=1), raw & 0xFFFFFFFF


def vector_answers():
    """The vectors of pull request 3: (id, octets, MAC length, the
    expected answer in the oracles' form)."""
    out = []
    for line in VECTORS.read_text(encoding="utf-8").splitlines():
        v = json.loads(line)
        req, exp = v["request"], v["expect"]
        b = bytes.fromhex(req["packet_hex"])
        if "error" in exp:
            ans = None
        else:
            hd = exp["header"]
            h = Header(hd["leap"], hd["version"], hd["mode"], hd["stratum"], hd["poll"], hd["precision"],
                       hd["root_delay_bits"], hd["root_dispersion_bits"], int(hd["reference_id_hex"], 16),
                       *(t["raw"] for t in hd["timestamps"]))
            fields = tuple((e["type"], bytes.fromhex(e["value_and_padding_hex"])) for e in exp["extensions"])
            ans = (h, fields, bytes.fromhex(exp["mac_hex"]), None)
        out.append((v["id"], b, req["mac_length"], ans))
    return out


def lean_version():
    try:
        out = subprocess.run(["lean", "--version"], cwd=ROOT, capture_output=True, text=True,
                             errors="backslashreplace", timeout=300)
        first = out.stdout.strip().splitlines()[:1]
        return first[0] if first else "unknown"
    except (OSError, subprocess.TimeoutExpired):
        return "unknown"


def count_arg(text):
    n = int(text)
    if n < 1:
        raise argparse.ArgumentTypeError("the count must be at least 1")
    return n


def write(lines):
    RESULTS.write_text("\n".join(lines), encoding="utf-8")


def code(text):
    """`text` as Markdown inline code, whatever backticks it holds."""
    return f"`` {text} ``" if "`" in text else f"`{text}`"


def tally(counter):
    return ", ".join(f"{k} {v}" for k, v in sorted(counter.items(), key=lambda kv: (-kv[1], kv[0])))


# ---------------------------------------------------------------------

ORACLE_ORDER = ("ntpd-rs", "NTPsec", "Wireshark", "ntplib")


def main():
    global EXE
    sys.set_int_max_str_digits(0)
    ap = argparse.ArgumentParser()
    ap.add_argument("--seed", type=int, default=20261028)
    ap.add_argument("--count", type=count_arg, default=20000)
    ap.add_argument("--no-oracles", action="store_true",
                    help="compare with the model only, as tests/plant_bugs.py does")
    ap.add_argument("--no-build", action="store_true",
                    help="use .lake/build/bin/ntp as it is, without `lake build ntp`")
    args = ap.parse_args()
    os.environ["PATH"] = f"{Path.home() / '.elan' / 'bin'}{os.pathsep}{os.environ.get('PATH', '')}"
    started = time.monotonic()

    def give_up(why):
        write(["# Test results", "", "- Oracle: none ran", f"- Seed: {args.seed}", "- Inputs: 0",
               f"- Failures: 1 ({why})", ""])
        sys.exit(why)

    if args.no_build:
        built = "`.lake/build/bin/ntp` as it was, not rebuilt (`--no-build`)"
        if not BUILT_EXE.exists():
            give_up("`--no-build`, and there is no .lake/build/bin/ntp")
        newest = max(p.stat().st_mtime for p in [ROOT / "Main.lean", ROOT / "Ntp" / "Spec" / "Defs.lean"]
                     + list((ROOT / "Ntp").glob("*.lean")))
        if BUILT_EXE.stat().st_mtime < newest:
            built += "; it is older than the sources"
    else:
        built = "built by `lake build ntp`"
        try:
            build = subprocess.run(["lake", "build", "ntp"], cwd=ROOT, capture_output=True, text=True,
                                   errors="backslashreplace", timeout=TIMEOUT)
            if build.returncode != 0:
                print(build.stdout + build.stderr)
                give_up("`lake build ntp` failed")
        except (OSError, subprocess.SubprocessError) as e:
            give_up(f"`lake build ntp` failed: {e}")

    failures = []
    with tempfile.TemporaryDirectory() as tmpname:
        tmp = Path(tmpname)
        EXE = tmp / "ntp"
        shutil.copy2(BUILT_EXE, EXE)
        exe_hash = hashlib.sha256(EXE.read_bytes()).hexdigest()

        # The oracles.
        oracles, described, left_out = {}, {}, []
        if args.no_oracles:
            left_out = [(name, "--no-oracles") for name in ORACLE_ORDER]
        else:
            for name, setup in (("ntpd-rs", lambda: setup_ntpdrs(tmp)), ("NTPsec", setup_ntpsec),
                                ("Wireshark", setup_tshark), ("ntplib", setup_ntplib)):
                handle, text = setup()
                if handle is None:
                    left_out.append((name, text))
                    print(f"oracle left out: {name}: {text}", flush=True)
                else:
                    oracles[name], described[name] = handle, text

        # The requests.
        items = inputs(args.seed, args.count)
        lines = [request(op, a) + ("\r\n" if i % 7 == 6 else "\n") for i, (_, op, a) in enumerate(items)]
        odd = MALFORMED + ODD
        digest = hashlib.sha256()
        for line in lines + [m + "\n" for m in odd]:
            digest.update(line.encode("utf-8"))
        inputs_digest = digest.hexdigest()
        served = {}

        def serve():
            served["out"] = run_parallel([str(EXE), "serve"], lines + [m + "\n" for m in odd], JOBS)

        server = threading.Thread(target=serve)
        server.start()
        wants = [model(op, a) for _, op, a in items]
        server.join()
        out, problems = served["out"]
        print(f"{len(items)} requests answered, {time.monotonic() - started:.0f} s", flush=True)
        for problem in problems:
            failures.append(("(whole run)", "a clean run", problem))
        tool, odd_out = out[:len(items)], out[len(items):]
        by_label = collections.Counter(f"{label} ({op})" for label, op, _ in items)
        by_op = collections.Counter(op for _, op, _ in items)
        refused = collections.Counter()
        accepted_shapes = collections.Counter()
        differ_model = 0
        spec_right = spec_total = 0
        autokey_stated = dict(autokey_cases())
        autokey_right = 0
        read_agrees = read_total = 0
        decoded = {}  # octets -> the tool's answer, parsed
        for i, ((label, op, a), (want, why), got) in enumerate(zip(items, wants, tool)):
            if op == "decode":
                b = a[0]
                read_total += 1
                r = show_answer(read(b)[0])
                if r == want:
                    read_agrees += 1
                else:
                    failures.append((f"the model's two readings of {short(hexd(b), 120)}", want, r))
                if why is not None:
                    refused[why] += 1
                else:
                    p = decode_spec(b)
                    mac = "none" if not p[2] else "a crypto-NAK" if len(p[2]) == 4 else f"{len(p[2])} octets"
                    accepted_shapes[(p[0].version, min(len(p[1]), 5), mac)] += 1
                try:
                    decoded.setdefault(b, parse_decoded(got))
                except ValueError:
                    decoded.setdefault(b, ("unreadable", got[:200]))
            if label == AUTOKEY_LABEL:
                if got == want == autokey_stated[a[0]]:
                    autokey_right += 1
                else:
                    failures.append((f"the Autokey field in {short(hexd(a[0]), 120)}", autokey_stated[a[0]],
                                     f"model {want}; tool {got}"))
            if label == "Ntp/Spec.lean's examples and rejects":
                spec_total += 1
                stated_answer = next(w for o, x, w in SPEC_CASES if o == op and x == a)
                spec_right += as_stated(want, stated_answer)
                if not as_stated(want, stated_answer):
                    failures.append((f"the model on {short(request(op, a), 120)}", stated_answer, want))
            if got != want:
                differ_model += 1
                failures.append((short(lines[i].rstrip("\r\n"), 160), short(want, 160), short(got, 160)))
        malformed_right = sum(1 for x in odd_out[:len(MALFORMED)] if x == "error")
        for m in MALFORMED:
            if model_line(m + "\n") != "error":
                failures.append((f"the model on {m!r}", "error", model_line(m + "\n")))
        odd_right = 0
        for m, x in zip(odd, odd_out):
            want = model_line(m + "\n")
            if x == want:
                odd_right += m in ODD
            else:
                failures.append((f"request {short(m, 100)!r}", short(want, 100), short(x, 100)))
        eof_right = 0
        for req, want in AT_EOF:
            if model_line(req) != want:
                failures.append((f"the model on {req!r} at end of input", want, model_line(req)))
            got, problem = run_lines([str(EXE), "serve"], [req], timeout=60)
            if got == [want] and not problem:
                eof_right += 1
            else:
                failures.append((repr(req) + " (at end of input)", want, f"{got} {problem or ''}".strip()))
        cli = cli_cases()
        cli_right, cli_failures = run_cli(cli)
        failures += cli_failures

        # Unix time: Figure 4 and datetime.
        fig4_right, fig4_total, fig4_named = 0, 0, collections.Counter()
        dt_right = dt_total = dt_outside = 0
        answers_by_request = {}
        for (label, op, a), got in zip(items, tool):
            if op in ("unix", "fromunix"):
                answers_by_request[(op, tuple(a))] = got
        for date, mjd, era, offset in ([] if args.no_oracles else FIGURE_4):
            unix_s = (mjd - UNIX_MJD) * 86400
            for op, a, want in (("unix", (era, offset * T32), f"OK {unix_s} 0"),
                                ("fromunix", (unix_s, 0), f"OK {era} {offset * T32}")):
                fig4_total += 1
                got = answers_by_request[(op, a)]
                if got == want:
                    fig4_right += 1
                elif offset == 0 and got == "FAIL":
                    fig4_named["Figure 4 gives 1 Jan 1900 the timestamp 0, which RFC 5905 section 6 makes "
                               "the value for unknown time: no Unix time, and no timestamp for that instant"] += 1
                else:
                    failures.append((f"Figure 4, {date}: {op} {a[0]} {a[1]}", want, got))
        for (op, a), got in ([] if args.no_oracles else answers_by_request.items()):
            if not got.startswith("OK "):
                continue
            x, y = (int(v) for v in got.split(" ")[1:])
            era, raw, s, f = (a[0], a[1], x, y) if op == "unix" else (x, y, a[0], a[1])
            d = datetime_unix(era, raw)
            if d is None:
                dt_outside += 1
                continue
            dt_total += 1
            if d == (s, f):
                dt_right += 1
            else:
                failures.append((f"datetime: {op} {a[0]} {a[1]}", f"OK {d[0]} {d[1]}", got))

        # The oracles.
        packets = list(decoded)
        comparisons = {}
        oracle_skipped = collections.Counter()
        for name in ORACLE_ORDER:
            if name not in oracles:
                continue
            t0 = time.monotonic()
            if name == "ntpd-rs":
                answers, problems = ntpdrs_answers(oracles[name], packets)
            elif name == "NTPsec":
                answers, problems = ntpsec_answers(oracles[name], packets)
            elif name == "Wireshark":
                answers, problems = tshark_answers(tmp, packets)
            else:
                answers, problems = ntplib_answers(oracles[name], packets)
            for problem in problems:
                failures.append((f"{name} (whole run)", "a clean run", problem))
            c = Comparison(name)
            for b, want in zip(packets, answers):
                if isinstance(want, str):
                    oracle_skipped[name] += 1
                    continue
                c.add(b, decoded[b], want)
            failures += c.failures
            comparisons[name] = c
            print(f"{name}: {c.asked} packets, {c.agree} agree, {time.monotonic() - t0:.0f} s", flush=True)

        # The vectors of pull request 3.
        vectors = vector_answers()
        pr3 = Comparison("ntp#3")
        pr3_rows = []
        for vid, b, mac_length, want in ([] if args.no_oracles else vectors):
            pr3.add(b, decoded[b], want, mac_length, label=f"vector {vid} (mac_length {mac_length})")
            got = VIEWS["ntp#3"](decoded[b])
            if got != want:
                pr3_rows.append((vid, mac_length, show_tail(got, want), show_tail(want, got),
                                 explain(b, "ntp#3", want, VIEWS["ntp#3"], mac_length)))
        failures += pr3.failures

    n_inputs = len(items) + len(odd) + len(AT_EOF) + len(cli)
    accepted = sum(accepted_shapes.values())
    lines_out = [
        "# Test results",
        "",
        "Written by `tests/run_tests.py`. Rerun it to check these numbers.",
        "",
        "- Oracle: the model of RFC 5905 and RFC 7822 in `tests/run_tests.py`, which every answer of the "
        "tool must equal",
    ]
    for name in ORACLE_ORDER:
        if name in described:
            lines_out.append(f"- Oracle: {described[name]}")
    if not args.no_oracles:
        lines_out += [
            "- Oracle: RFC 5905 Figure 4, with errata 4025 and 6524, and Python's datetime module "
            f"(Python {sys.version.split()[0]}), for the Unix times",
            "- Oracle: the 79 vectors of Proven-Commons/ntp pull request 3 (orda-aska, commit cc5dab4), in "
            "`tests/ntp-3-wire-vectors.jsonl`"]
    lines_out += [
        "- Oracles left out: " + ("; ".join(f"{n} ({why})" for n, why in left_out) or "none")
        + "; and dropped: chrony's parser (the session that wrote these tests was not permitted to build "
        "chrony's downloaded source for a harness)",
        f"- Lean: {lean_version()}",
        f"- Executable: {built}; SHA-256 of the copy run {exe_hash}",
        f"- Seed: {args.seed}",
        f"- Count: {args.count}",
        f"- Inputs: {n_inputs}",
        f"- Inputs SHA-256: {inputs_digest}, of the request lines, in order; a rerun with the same seed and "
        "count must give the same",
        "- By kind: " + ", ".join(f"{k} {v}" for k, v in sorted(by_label.items())),
        "- Requests: " + ", ".join(f"`{op}` {n}" for op, n in sorted(by_op.items()))
        + f", malformed {len(MALFORMED)}, odd {len(ODD)}, at the end of input {len(AT_EOF)}, command line "
        f"{len(cli)}",
        f"- Answers that differ from the model: {differ_model}",
        f"- Ntp/Spec.lean's `examples` and `rejects`, answered by the model as Ntp/Spec.lean states them: "
        f"{spec_right} of {spec_total}",
        f"- The model's two readings of each `decode` input, by `Valid` and `packetBytes` and by SPEC.md's "
        f"one-pass rule, the same: {read_agrees} of {read_total}",
        f"- Autokey fields (RFC 5906 Figure 7) whose Value Length runs past the field, as in CVE-2014-9750, "
        f"read by their own Length with their octets unchanged, by the tool and the model: {autokey_right} "
        f"of {by_label[AUTOKEY_LABEL + ' (decode)']}",
        f"- Packets: {by_op['decode']}, of which the model reads {accepted}; why it refuses the others: "
        + (tally(refused) or "none"),
        "- Packets the model reads, by version, number of extension fields and MAC: "
        + ", ".join(f"version {v}, {k}{'+' if k == 5 else ''} fields, MAC {m}: {n}"
                    for (v, k, m), n in sorted(accepted_shapes.items())),
        f"- Malformed requests answered `error`: {malformed_right} of {len(MALFORMED)}; odd but "
        f"well-formed requests answered as the model says: {odd_right} of {len(ODD)}",
        f"- Requests ending in CR LF: every seventh, {len(items) // 7}",
        f"- Last lines sent alone, with no LF, with CR LF, or with a lone CR, answered right: "
        f"{eof_right} of {len(AT_EOF)}",
        f"- Command line (`ntp serve` and wrong arguments), printing and exiting as the header of Main.lean "
        f"says: {cli_right} of {len(cli)}",
    ]
    if args.no_oracles:
        lines_out.append("- RFC 5905 Figure 4, Python's datetime and the vectors of pull request 3: left out "
                         "(--no-oracles)")
    else:
        lines_out += [
            f"- RFC 5905 Figure 4 (`unix` of each row's era and offset, and `fromunix` of its MJD as Unix "
            f"time): {fig4_right} of {fig4_total} as the table gives them; named differences: "
            + (tally(fig4_named) or "none"),
            f"- Unix times the tool gives (`unix` answers, and the requests of `fromunix` answers), as "
            f"Python's datetime gives them: {dt_right} of {dt_total}; outside datetime's years 1 to 9999: "
            f"{dt_outside}"]
    for name in ORACLE_ORDER:
        if name not in comparisons:
            lines_out.append(f"- {name}: left out")
            continue
        c = comparisons[name]
        named = sum(n for n, _ in c.named.values())
        lines_out.append(
            f"- {name}: {c.asked} distinct packets"
            + (f" ({oracle_skipped[name]} more not sent: longer than tshark's {TSHARK_MAX}-octet frames)"
               if oracle_skipped[name] else "")
            + f"; the same answer as the tool: {c.agree} (of the {c.asked_read} the tool reads: "
            f"{c.agree_read}); named differences: {named}; the model with {name}'s choices gives its "
            f"answer: {c.model_right} of {c.asked}")
    named = sum(n for n, _ in pr3.named.values())
    if not args.no_oracles:
        lines_out.append(f"- Pull request 3: {pr3.asked} vectors; the same answer as the tool: {pr3.agree}; "
                         f"named differences: {named}; the model with its choices gives the vector's answer: "
                         f"{pr3.model_right} of {pr3.asked}")
    lines_out += [
        f"- Time: {time.monotonic() - started:.0f} s",
        f"- Failures: {len(failures)}",
        "",
    ]
    if not args.no_oracles:
        lines_out += ["## Where the oracles and the tool differ", "",
                      "Each difference is counted under the smallest set of the oracle's choices with which "
                      "the model gives the oracle's answer, so the choices named are the ones that make the "
                      "difference. The first case that showed each is given.", ""]
        for name in ORACLE_ORDER:
            if name not in comparisons:
                continue
            c = comparisons[name]
            lines_out += [f"### {name}", "", f"The choices of {name} that the model can switch on:", ""]
            lines_out += [f"{k}. {rule}" for k, rule in enumerate(ORACLE_RULES[name], 1)]
            lines_out += ["", "The differences, by the choices that make them:", ""]
            if not c.named:
                lines_out.append("No difference.")
            for rules, (n, example) in sorted(c.named.items(), key=lambda kv: -kv[1][0]):
                lines_out.append(f"- {tags(name, rules)}: {n}. For example {example}")
            lines_out.append("")
        lines_out += ["### Pull request 3", "", "The choices of its contract that the model can switch on:", ""]
        lines_out += [f"{k}. {rule}" for k, rule in enumerate(ORACLE_RULES["ntp#3"], 1)]
        lines_out += ["", "Each vector whose answer differs from the tool's, with the choices that give the "
                      "vector's answer:", ""]
        for vid, mac_length, tool_answer, want, rules in pr3_rows:
            lines_out.append(f"- `{vid}` (mac_length {mac_length}), {tags('ntp#3', rules or ())}: the vector "
                             f"{short(want, 160)}; the tool {short(tool_answer, 160)}")
        lines_out.append("")
    if failures:
        lines_out += ["## Failures", ""]
        lines_out += [f"- {code(short(req, 300))}: expected {code(short(want, 300))}, got {code(short(got, 300))}"
                      for req, want, got in failures[:60]]
        if len(failures) > 60:
            lines_out.append(f"- and {len(failures) - 60} more")
        lines_out.append("")
    write(lines_out)
    print(f"{n_inputs} inputs, {len(failures)} failures; results in {RESULTS}")
    return 1 if failures else 0


if __name__ == "__main__":
    sys.exit(main())
