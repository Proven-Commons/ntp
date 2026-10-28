# Specification: ntp

NTP, the Network Time Protocol, sends its time in one UDP packet: RFC 5905 ("Network Time Protocol Version 4: Protocol and Algorithms Specification") gives the packet, and RFC 7822 ("Network Time Protocol Version 4 (NTPv4) Extension Fields") updates its section 7.5 on extension fields. This library reads and writes one packet, the whole of one UDP payload:

- the 48-octet header (RFC 5905 Figure 8 and section 7.3);
- the extension fields after it (RFC 7822 section 3, Figure 14), each as its Field Type and its octets;
- the MAC at the end, as its octets.

It also converts a 64-bit timestamp to Unix time and back, given the era, which is not in the packet (RFC 5905 section 6).

It does not check a MAC, read what an extension field holds, or run any part of the protocol: no clock filter, peer selection or clock discipline, no Autokey (RFC 5906) and no Network Time Security (RFC 8915). "Not in this slice" below lists what else it leaves out.

A reviewer who did not write this specification approves it. The approval also covers `Spec.lean`, `Spec/Defs.lean`, `Spec/Examples.lean`, and the other files that `bar.toml` lists.

## The header

`Spec.Header` has the fields of Figure 8, in its order, and `Spec.headerBytes` writes them as their 48 octets, every multi-octet field big-endian:

| Octets | Field | Kept as |
|---|---|---|
| 0, top 2 bits | LI, the "2-bit integer warning of an impending leap second" (Figure 9) | 0 to 3 |
| 0, next 3 bits | VN, the "3-bit integer representing the NTP version number" | 0 to 7 |
| 0, low 3 bits | Mode, the "3-bit integer representing the mode" (Figure 10) | 0 to 7 |
| 1 | Stratum, an "8-bit integer" (Figure 11) | 0 to 255 |
| 2 | Poll, an "8-bit signed integer", in log2 seconds | -128 to 127 |
| 3 | Precision, an "8-bit signed integer", in log2 seconds | -128 to 127 |
| 4 to 7 | Root Delay, in "NTP short format" | its 32 bits, as a number |
| 8 to 11 | Root Dispersion, in "NTP short format" | its 32 bits, as a number |
| 12 to 15 | Reference ID, a "32-bit code" | its 32 bits, as a number, the first octet most significant |
| 16 to 23 | Reference Timestamp, in "NTP timestamp format" | its 64 bits, as a number |
| 24 to 31 | Origin Timestamp | its 64 bits |
| 32 to 39 | Receive Timestamp | its 64 bits |
| 40 to 47 | Transmit Timestamp | its 64 bits |

Poll and Precision are two's complement. The short format is 16 bits of seconds and 16 of fraction, and the timestamp format 32 bits of seconds and 32 of fraction (section 6); this library keeps each as the number its bits hold and does not divide it.

`Spec.HeaderValid` says which headers this reader accepts:

- every field fits in its bits;
- the version is 3 or 4. VN is "currently 4", and the header "fields are backwards compatible with NTPv3" (RFC 1305). Versions 1 and 2 are refused, and so are 0, 5, 6 and 7;
- the mode is 1 to 5: symmetric active, symmetric passive, client, server and broadcast. Mode 0 is "reserved", mode 6 is "NTP control message" and mode 7 is "reserved for private use" (Figure 10). The packets of modes 6 and 7 are not in the format of Figure 8, so they are refused.

Any leap indicator, stratum, poll and precision is accepted, including stratum 0 (the kiss-o'-death packet of section 7.4) and the "reserved" strata 17 to 255.

## Extension fields and the MAC

After the header come "optional extension fields and finally an optional message authentication code (MAC) consisting of the Key Identifier field and Message Digest field" (RFC 5905 7.3).

**Extension fields.** `Spec.ExtField` is a field of Figure 14: its 16-bit Field Type, then its Value and its Padding, kept together, since where the Value ends is "specific to the defined function". `Spec.extBytes` writes it as the Field Type, the Length, then those octets. The Length "indicates the length of the entire extension field in octets, including the Padding field", so it counts the four octets of Field Type and Length too. `Spec.ExtValid` says which fields this reader accepts, from RFC 7822 section 3:

- the Length is a multiple of 4: "All extension fields are zero-padded to a word (four octets) boundary";
- the Length is at least 16: "the minimum field length containing required fields is four words (16 octets)";
- the Length is at most 65532: "the maximum field length cannot be longer than 65532 octets, due to the maximum size of the Length field".

Any Field Type is accepted, and the Value and Padding are given as they are. RFC 7822 says a host "SHOULD ignore" a field of unknown type; which types to act on is for the program using this library. The Padding is not checked to be zero, since this library cannot tell where it starts.

**The MAC.** `Spec.MacValid` says which MACs this reader accepts:

- none;
- 20 or 24 octets: the 32-bit Key Identifier, then a 128-bit digest (RFC 5905 7.3) or a 160-bit one. "This field can be either 24 octets long, 20 octets long, or a 4-octet crypto-NAK" (RFC 7822 section 1), and "A MAC MUST NOT be longer than 24 octets if there is no extension field present, unless a longer MAC is agreed upon by both client and server" (7.5.1.3);
- the crypto-NAK: "a MAC consisting of four octets of zeros" (RFC 5905 9.2), "the key identifier with value zero" (A.5), in a packet with no extension field.

**`Spec.Valid`** says which packets this reader accepts:

- the header is valid, each extension field is valid, and the MAC is one of the above;
- a version 3 packet has no extension fields. RFC 7822 starts its section 7.5 with "In NTPv4, one or more extension fields can be inserted after the header and before the MAC", and RFC 1305 has a header and an optional authenticator only;
- without a MAC, the last extension field is at least 28 octets: "If the packet includes a single extension field, the length of the extension field MUST be at least 7 words, i.e., at least 28 octets. If the packet includes more than one extension field, the length of the last extension field MUST be at least 28 octets. The length of the other extension fields in this case MUST be at least 16 octets each" (7.5.1.4).

`Spec.packetBytes` writes a packet as its header, its extension fields in order, then its MAC.

### Reading the octets after the header

The rules above are the ones that let a receiver tell the last extension field from a MAC without knowing the MAC's length beforehand. A reader can follow them in one pass, as chrony 4.6.1 does for version 4 (`parse_packet` in `ntp_core.c`), and this library reads the octets after the header so:

1. Four zero octets are a crypto-NAK.
2. In version 3, no octets, or 20 or 24 octets, are the MAC. Anything else is refused.
3. In version 4, while more than 24 octets are left, a field starts there: a Field Type, then a Length that must be a multiple of 4, at least 16, and no more than the octets left. When 24 or fewer octets are left, they must be none, or 20 or 24, the MAC. Anything else is refused.

This accepts exactly the valid packets, and reads each one way only. With a MAC of 20 or 24 octets, every field leaves more than 24 octets before it is read, so each is read as a field, and then the MAC is what is left. Without a MAC, the last field is all that is left when it is read, so it is more than 24 octets, a multiple of 4, and so at least 28. A field can never be read as part of the MAC, nor the MAC as a field. `Spec.decode_iff` proves that the reader accepts exactly the octets `Spec.packetBytes` writes for a valid packet.

So 24 or fewer octets after the header are never an extension field. In particular, 24 octets that begin like a field of Length 24 are a MAC. A sender that put that field in a packet without a MAC broke 7.5.1.4, and this reader reads it as the MAC.

### Choices where readers differ

- **Versions 1 and 2** are refused. chrony and ntpd accept them.
- **Version 3 with octets after the header.** chrony takes any octets after a version 3 header as a MAC, including the 72-octet extended authenticator of MS-SNTP. ntpd 4.2.8p18 walks them as extension fields. This reader follows the RFCs: version 3 has no extension fields, and its MAC is 4 zero octets, 20 octets or 24 octets.
- **MAC lengths.** chrony takes 20 to 24 octets left after the extension fields as the MAC, but first refuses a packet whose length is not a multiple of 4, so in effect 20 or 24, as here. A MAC longer than 24 octets is refused, unless its octets happen to read as fields and a MAC; a length agreed by other means is not in the packet, so this reader cannot use it.
- **The crypto-NAK** is four zero octets, in a packet with no extension field. chrony requires the same. The pseudocode of RFC 5905 A.5.1 treats any MAC of four octets as a crypto-NAK; four octets that are not zero are refused here.
- **Autokey's 8-octet fields.** RFC 5906 section 10 allows extension fields of 8 octets. RFC 7822 sets the minimum at 16, and this reader follows it.
- **No largest packet.** Any number of octets is read. chrony's packet buffer holds at most 1024 octets of extension fields and a MAC (`NTP_MAX_EXTENSIONS_LENGTH` in `ntp.h`).

## Timestamps

A timestamp is 32 bits of seconds and 32 bits of fraction from the start of its era. "The prime epoch, or base date of era 0, is 0 h 1 January 1900 UTC", and to find the time from an era and a timestamp, "s = era * 2^(32) + timestamp" (RFC 5905 section 6). The era is not in the packet: a program knows it from its own clock. So the conversion takes the era as an argument, and it may be any integer, negative for dates before 1900.

**`Ntp.toUnix era raw`** gives the Unix time of the 64-bit timestamp `raw` in era `era`: the seconds from 1900, `era * 2^32 + raw / 2^32`, less the 2,208,988,800 seconds from 1900 to 1970 (Figure 4: "1 Jan 1970 ... 2,208,988,800 First day UNIX"), plus the fraction `raw mod 2^32` in units of 2^-32 seconds. It gives the whole seconds, which may be negative, and the fraction, below 2^32. It is exact. It gives nothing for a raw value of 0: "a value of zero is a special case representing unknown or unsynchronized time" (section 6), in every era. A value of more than 64 bits gives nothing either.

**`Ntp.fromUnix seconds fraction`** gives the era and the 64-bit timestamp of a Unix time, by the rule of section 6, "era = s / 2^(32) and timestamp = s - era * 2^(32), which works for positive and negative dates", with the division rounding down. It gives nothing for a fraction of 2^32 or more. The first instant of each era, such as 1900-01-01 00:00:00 UTC and 2036-02-07 06:28:16 UTC, would have the timestamp 0, which means unknown, so it gives nothing for them either.

Neither NTP timestamps nor Unix time count leap seconds, so the offset between them is the fixed one of Figure 4. What happens during a leap second is outside this library.

## What must always hold

Each property is a theorem in `Spec.lean`, under the name given.

| Property | Theorem |
|----------|---------|
| The decoder accepts exactly the octets of a valid packet, and gives that packet: its header fields, its extension fields and its MAC. So it reads each accepted payload one way only. | `Spec.decode_iff` |
| The encoder writes every valid packet as `Spec.packetBytes` lays it out. | `Spec.encode_eq` |
| Encoding a packet and decoding the octets gives the packet back exactly when it is valid. | `Spec.decode_encode` |
| Encoding a decoded packet gives back the octets it was read from. | `Spec.encode_decode` |
| A payload shorter than 48 octets is refused. | `Spec.decode_short` |
| A packet of a version other than 3 or 4 is refused. | `Spec.decode_version` |
| A packet of mode 0, 6 or 7 is refused. | `Spec.decode_mode` |
| An extension field whose Length runs past the end of the packet is refused, wherever it is and whatever the rest of the packet holds. | `Spec.decode_ext_overrun` |
| The timestamp 0 has no Unix time, in any era. | `Spec.toUnix_zero` |
| The Unix time of a timestamp in an era is exactly `era * 2^32 + raw / 2^32 - 2208988800` seconds, given as whole seconds and a fraction in units of 2^-32 seconds. | `Spec.toUnix_spec` |
| Converting a timestamp to Unix time and back gives the era and the timestamp back, and converting a Unix time to a timestamp and back gives the Unix time back. | `Spec.fromUnix_toUnix`, `Spec.toUnix_fromUnix` |
| Examples: a client request and a server reply captured on a network, read field by field; a captured Network Time Security reply with two extension fields; packets with two fields and a MAC, a crypto-NAK, a version 3 packet with a MAC, and 24 octets read as a MAC; the Unix time of a captured timestamp; the end of era 0 in 2036 and the end of era -1 in 1899. | `Spec.examples` |
| Fourteen packets that each break one rule are refused, and a reader without that rule accepts each: versions 2 and 5; modes 0, 6 and 7; 47 octets; a field of Length 12; a Length not a multiple of 4; a Length past the end; a last field of 16 octets without a MAC; four octets after the header that are not zero; a field followed by a crypto-NAK; a field in a version 3 packet; 21 octets after the header. | `Spec.rejects` |

`Spec.decode_short`, `Spec.decode_version`, `Spec.decode_mode` and `Spec.decode_ext_overrun` say what is refused, and a decoder that refuses everything meets them. `Spec.decode_iff` and `Spec.examples` rule that decoder out. The same holds for `Spec.toUnix_zero`, which `Spec.toUnix_spec` pairs, and for `Spec.toUnix_fromUnix`, which `Spec.fromUnix_toUnix` pairs. Since `Spec.decode_iff` is exact, it fixes what the decoder gives for every input; `Spec.toUnix_spec` does the same for `Ntp.toUnix`, and the two round trips together for `Ntp.fromUnix`.

**CVE-2014-9750.** ntpd before 4.2.8p1 read past the end of its buffer when an Autokey extension field held "an invalid value for the length of its value field": it followed a length inside the packet without checking it against what holds it. At the level this library reads, the length to check is each field's Length, and `Spec.decode_ext_overrun` proves that a Length that runs past the end of the packet is refused. The Value Length inside an Autokey field (RFC 5906 Figure 7) is part of the field's octets, which this library gives as they are and does not read.

## Not in this slice

- **The MAC.** It is given as its octets; no digest is computed or checked, and no key is looked up.
- **What extension fields hold.** Autokey (RFC 5906), Network Time Security (RFC 8915) and every other field type are given as their octets, and lengths inside them are not read.
- **The meaning of header fields.** The Reference ID is a number, whether it is a kiss code, an IPv4 address or part of a hash; the root delay and dispersion are their bits; nothing checks that the timestamps fit together.
- **Modes 6 and 7.** Their formats are other than Figure 8, and they are refused.
- **Which era a timestamp is in.** The program using this library gives it.
- **Leap seconds**, and time zones.
- **The protocol.** No on-wire exchange, clock filter, selection, clustering or discipline.
- **Encoding a packet that is not valid.** What `Ntp.encode` writes for one is not specified. `Spec.decode_encode` shows how to tell: decoding what it wrote gives the packet back exactly when it was valid.

## The command-line tool

`Main.lean` has one mode. `ntp serve` answers requests from the differential tests, one per line: decode a packet, encode one, and convert a timestamp to Unix time and back. The header comment of `Main.lean` gives the protocol. Every answer comes from the functions above.
