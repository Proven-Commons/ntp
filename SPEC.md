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
- the version is 3 or 4. VN is "currently 4", and the header "fields are backwards compatible with NTPv3" (RFC 5905 7.3); NTPv3 is RFC 1305. Versions 1 and 2 are refused, and so are 0, 5, 6 and 7;
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

These are the MACs of NTPv4. This reader takes the same ones in version 3, which is its own choice: RFC 1305 gives version 3 a 12-octet authenticator, which this reader refuses (see "Choices where readers differ").

**`Spec.Valid`** says which packets this reader accepts:

- the header is valid, each extension field is valid, and the MAC is one of the above;
- a version 3 packet has no extension fields. RFC 7822 starts its section 7.5 with "In NTPv4, one or more extension fields can be inserted after the header and before the MAC". This too is this reader's choice, where readers differ (see "Choices where readers differ");
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

The rules above are this reader's. Other readers of the packet choose differently in places, and where the RFCs leave a choice open, this section says so. chrony 4.6.1 and ntpd 4.2.8p18 are described from their source, which was read but not run: `parse_packet` in chrony's `ntp_core.c`, and `receive` and `valid_NAK` in ntpd's `ntp_proto.c`, with `MIN_MAC_LEN` and `MAX_MAC_LEN` in its `ntp.h`. ntpd-rs, NTPsec and Wireshark were run by the tests, and `tests/TEST-RESULTS.md` counts each of their differences under the choice that makes it.

- **Versions 1 and 2** are refused. chrony and ntpd accept them, and NTPsec and Wireshark read every version.
- **Version 3 with octets after the header.** Here the RFCs do not give this reader its rule; the rule is its own choice. RFC 1305, NTPv3, gives an authenticator of "96 bits, including a 32-bit key identifier and 64-bit crypto-checksum" (12 octets, for DES), and lets "additional information" go "between the (padded) NTP message and the key identifier". The crypto-NAK (RFC 5905 9.2) and the MACs of 20 and 24 octets (RFC 5905 7.3, RFC 7822 section 1) are NTPv4's; RFC 5905 says only that its symmetric key scheme "has been carried over from NTPv3". This reader reads version 3 with no extension fields, which RFC 7822 gives to NTPv4, and with the MACs of version 4: none, the crypto-NAK, 20 or 24 octets. So it refuses RFC 1305's 12-octet authenticator, and every other tail. The other readers:
  - chrony takes any whole number of words after a version 3 header as the MAC, including the 72-octet extended authenticator of MS-SNTP;
  - ntpd takes 4 to 24 octets, in steps of 4, as the MAC ("if 3 [words], the packet is authenticated with DES"), and walks a longer tail as extension fields, as in version 4;
  - ntpd-rs takes any 4 to 24 octets as the MAC;
  - NTPsec reads version 3 as version 4, extension fields too.
- **MAC lengths in version 4.** After the extension fields, this reader takes none, 20 or 24 octets as the MAC, following RFC 7822 (sections 1 and 7.5.1.3, and 7.5.1.4, which makes a last field without a MAC at least 28 octets). So does chrony: it takes 20 to 24 octets, but first refuses a packet whose length is not a multiple of 4. A MAC longer than 24 octets is refused, unless its octets happen to read as fields and a MAC; a length agreed by other means is not in the packet, so this reader cannot use it. The other readers:
  - ntpd takes any 4 to 24 octets left after the fields, in steps of 4, as the MAC (`MIN_MAC_LEN` is one word and `MAX_MAC_LEN` six): 8, 12 (DES) and 16 octets too, and 4 octets after a field. Such a MAC then fails to authenticate without a matching key, but the packet is not dropped as malformed. So ntpd reads a field of 28 octets and 16 octets after it as a field and a MAC, where this reader refuses them (`Spec.rejects`);
  - ntpd-rs takes any 4 to 24 octets as the MAC, whatever they hold, 21 to 23 too;
  - NTPsec takes 4, 20 or 24 octets as the MAC (any 4 octets as a crypto-NAK, after fields too), refuses the packet with 8, 12 or 16, and with any other number of octets left reads the packet and passes over those octets without a word;
  - Wireshark takes as the MAC whatever its own split leaves (below).
- **The crypto-NAK** is four zero octets, in a packet with no extension field, of any mode from 1 to 5. chrony requires the same. The pseudocode of RFC 5905 A.5.1 treats any MAC of four octets as a crypto-NAK; four octets that are not zero are refused here, and by ntpd (`valid_NAK`), while NTPsec and ntpd-rs take them. ntpd also drops four zero octets in a packet whose mode is not 1, 2 or 4 ("Only server responses can contain NAK's"), and checks a crypto-NAK against its own state: a peer with a key, and the origin timestamp of its request. This reader takes a crypto-NAK in a client request (mode 3) and a broadcast (mode 5) too: whether it means anything there is for the protocol, which this library does not run.
- **The least extension field.** RFC 7822 sets the least Length at 16 (section 3), and this reader and chrony follow it. RFC 5906 section 10 allows Autokey fields of 8 octets. ntpd takes any Length of 4 or more that is a multiple of 4 and fits, where more than 24 octets are left, and ntpd-rs's least Length is 4 too, so both read fields of Length 4, 8 and 12, which this reader refuses.
- **NTPsec** reads an extension field as a 32-bit type and a 32-bit length of the value after them, with no padding or minimum, cut short at the end of the packet, not as RFC 7822 Figure 14 lays it out; so it takes a field that runs past the end of the packet. It also reads Poll as unsigned, where RFC 5905 7.3 says "signed".
- **Wireshark** splits the octets after the header its own way, in every version: fields while 16 or more octets are left, each of a Length of 16 or more that fits; then, when 1 to 19 octets are left that are not a crypto-NAK, it gives the last field back to the MAC; whatever is left is the MAC, of any length.
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
| An extension field whose Length runs past the end of the packet is refused, wherever it starts with more than 24 octets left, and whatever the rest of the packet holds. (24 or fewer octets left are never a field: they are read as the MAC, or refused.) | `Spec.decode_ext_overrun` |
| The timestamp 0 has no Unix time, in any era. | `Spec.toUnix_zero` |
| The Unix time of a timestamp in an era is exactly `era * 2^32 + raw / 2^32 - 2208988800` seconds, given as whole seconds and a fraction in units of 2^-32 seconds. | `Spec.toUnix_spec` |
| Converting a timestamp to Unix time and back gives the era and the timestamp back, and converting a Unix time to a timestamp and back gives the Unix time back. | `Spec.fromUnix_toUnix`, `Spec.toUnix_fromUnix` |
| Examples: a client request and a server reply captured on a network, read field by field; a captured Network Time Security reply with two extension fields; packets with two fields and a MAC, a crypto-NAK, a version 3 packet with a MAC, and 24 octets read as a MAC; an Autokey field whose Value Length runs past the field, read by its own Length and given back as it is; the Unix time of a captured timestamp; the end of era 0 in 2036 and the end of era -1 in 1899. | `Spec.examples` |
| Fourteen packets that each break one rule are refused, and each comes after a packet that differs from it only there and is accepted: versions 2 and 5; modes 0, 6 and 7; 47 octets; a field of Length 12; a Length not a multiple of 4; a Length past the end; a last field of 16 octets without a MAC; four octets after the header that are not zero; a field followed by a crypto-NAK; a field in a version 3 packet; 21 octets after the header. | `Spec.rejects` |

`Spec.decode_short`, `Spec.decode_version`, `Spec.decode_mode` and `Spec.decode_ext_overrun` say what is refused, and a decoder that refuses everything meets them. `Spec.decode_iff`, `Spec.examples` and the accepted packets of `Spec.rejects` rule that decoder out. `tests/plant_bugs.py` plants a reader without each rule that `Spec.rejects` breaks, and the tests catch each one (`tests/PLANTED-BUGS.md`). The same holds for `Spec.toUnix_zero`, which `Spec.toUnix_spec` pairs, and for `Spec.toUnix_fromUnix`, which `Spec.fromUnix_toUnix` pairs. Since `Spec.decode_iff` is exact, it fixes what the decoder gives for every input; `Spec.toUnix_spec` does the same for `Ntp.toUnix`, and the two round trips together for `Ntp.fromUnix`.

**CVE-2014-9750.** ntpd before 4.2.8p1, with Autokey enabled, could leak its memory or crash on "a packet containing an extension field with an invalid value for the length of its value field" (ntp bug 2671: "vallen is not validated"): it followed a length from the packet without checking it against what holds it. That length, the Value Length inside an Autokey field (RFC 5906 Figure 7), is part of the field's octets, which this library gives as they are and does not read. `Spec.examples` reads a packet whose Autokey field of 28 octets has a Value Length of 0xFFFFFFFF: the field is read by its own Length, and its octets come back unchanged. A program that reads the Value Length must check it against the field. The same flaw at the level this library reads would be a field's own Length that runs past the end of the packet, and `Spec.decode_ext_overrun` proves that such a field is refused.

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
