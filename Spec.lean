import Ntp
import Spec.Defs
import Spec.Examples

/-!
  The statements a reviewer approves. Each `sorry` is proved under the
  same name in `Proofs/`, and `lake comparator` checks that each proof
  proves exactly the statement here.

  `Spec/Defs.lean` writes the packet down from RFC 5905 and RFC 7822.
  The code is in `Ntp/`.
-/

namespace Spec

/-- The decoder accepts exactly the octets of a valid packet, and gives
    that packet. So each accepted input is read one way only, and every
    field it gives is the field the octets hold. -/
theorem decode_iff (b : List UInt8) (p : Packet) :
    Ntp.decode b = some p ↔ Valid p ∧ b = packetBytes p := by
  sorry

/-- The encoder writes every valid packet as RFC 5905 Figure 8 and RFC
    7822 Figure 14 lay it out. -/
theorem encode_eq (p : Packet) (hp : Valid p) : Ntp.encode p = packetBytes p := by
  sorry

/-- Encoding a packet and decoding the octets gives the packet back
    exactly when it is valid. -/
theorem decode_encode (p : Packet) : Ntp.decode (Ntp.encode p) = some p ↔ Valid p := by
  sorry

/-- Encoding a decoded packet gives back the octets it was read from. -/
theorem encode_decode (b : List UInt8) (p : Packet) (h : Ntp.decode b = some p) :
    Ntp.encode p = b := by
  sorry

/-- A payload shorter than the 48-octet header is refused, whatever it
    holds. -/
theorem decode_short (b : List UInt8) (h : b.length < 48) : Ntp.decode b = none := by
  sorry

/-- A packet whose version (VN, the three bits after the two of LI at
    the start of the first octet: `x / 8 % 8`) is not 3 or 4 is refused,
    whatever follows. -/
theorem decode_version (x : UInt8) (b : List UInt8)
    (h : x.toNat / 8 % 8 ≠ 3 ∧ x.toNat / 8 % 8 ≠ 4) : Ntp.decode (x :: b) = none := by
  sorry

/-- A packet whose mode, the low three bits of the first octet, is 0
    (reserved), 6 (control message) or 7 (private use) is refused,
    whatever follows. -/
theorem decode_mode (x : UInt8) (b : List UInt8)
    (h : x.toNat % 8 = 0 ∨ x.toNat % 8 = 6 ∨ x.toNat % 8 = 7) : Ntp.decode (x :: b) = none := by
  sorry

/-- An extension field whose Length runs past the end of the packet is
    refused: after any 48 octets and any valid extension fields, where
    more than 24 octets are left (so a field starts there, not the MAC),
    a field whose Length is more than the octets left makes the whole
    packet refused, whatever the other octets hold. A reader that reads
    past the end, or cuts the field short at the end, accepts some of
    these. -/
theorem decode_ext_overrun (h : List UInt8) (es : List ExtField) (type len : Nat)
    (r : List UInt8) (hh : h.length = 48) (hes : ∀ e ∈ es, ExtValid e) (hlen : len < 2 ^ 16)
    (hr : 24 < 4 + r.length) (hover : 4 + r.length < len) :
    Ntp.decode (h ++ es.flatMap extBytes ++ beBytes 2 type ++ beBytes 2 len ++ r) = none := by
  sorry

/-- A raw timestamp of 0 means unknown in every era: "a value of zero is
    a special case representing unknown or unsynchronized time" (RFC 5905
    section 6). It has no Unix time. -/
theorem toUnix_zero (era : Int) : Ntp.toUnix era 0 = none := by
  sorry

/-- The exact Unix time of a timestamp. In era `era`, the nonzero 64-bit
    timestamp `raw` is `era * 2^32 + raw / 2^32` seconds from 1900
    (RFC 5905 section 6: "s = era * 2^(32) + timestamp", the low 32 bits
    being the fraction), so `era * 2^32 + raw / 2^32 - 2208988800`
    seconds from 1970. `toUnix` gives it as whole seconds `s` and a
    fraction `f` below 2^32, in units of 2^-32 seconds: exactly when
    `s + f / 2^32` is that number, multiplied out below by 2^32. A raw
    value of 0, or of more than 64 bits, gives `none`. -/
theorem toUnix_spec (era : Int) (raw : Nat) (s : Int) (f : Nat) :
    Ntp.toUnix era raw = some (s, f) ↔
      raw ≠ 0 ∧ raw < 2 ^ 64 ∧ f < 2 ^ 32 ∧
        s * 2 ^ 32 + f = era * 2 ^ 64 + raw - unixEpoch * 2 ^ 32 := by
  sorry

/-- `fromUnix` gives back the era and timestamp of every Unix time that
    `toUnix` gives. -/
theorem fromUnix_toUnix (era : Int) (raw : Nat) (s : Int) (f : Nat)
    (h : Ntp.toUnix era raw = some (s, f)) : Ntp.fromUnix s f = some (era, raw) := by
  sorry

/-- What `fromUnix` gives, `toUnix` takes back to the same Unix time. -/
theorem toUnix_fromUnix (s : Int) (f : Nat) (era : Int) (raw : Nat)
    (h : Ntp.fromUnix s f = some (era, raw)) : Ntp.toUnix era raw = some (s, f) := by
  sorry

/-- Worked by hand:
    - the captured client request and server reply, read field by field,
      with no extension field and no MAC;
    - a captured Network Time Security reply with two extension fields
      and no MAC;
    - the client request with fields of 16 and 20 octets and a 20-octet
      MAC;
    - a crypto-NAK, and a version 3 packet with a MAC;
    - 24 octets after the header that begin like a field of Length 24:
      they are the MAC;
    - an Autokey field whose Value Length, 0xFFFFFFFF, runs far past the
      field, as in CVE-2014-9750, then a MAC: the field is read by its
      own Length, and its octets come back as they are;
    - the transmit timestamp of the reply, 2022-04-05 06:43:52 UTC, and
      the Unix epoch;
    - the end of era 0 in 2036: the last whole second of era 0, then the
      raw value 2^32 in era 0 (in 1900) and in era 1 (in 2036), the raw
      value 0 in era 1, which means unknown, and so no timestamp for
      2036-02-07 06:28:16 UTC, the first instant of era 1;
    - the last second of era -1, in 1899. -/
theorem examples :
    Ntp.decode clientRequest = some { header := clientHeader, exts := [], mac := [] } ∧
    Ntp.decode serverReply = some { header := serverHeader, exts := [], mac := [] } ∧
    Ntp.decode ntsReply =
      some { header := ntsHeader,
             exts := [{ type := 0x0104, body := (ntsReply.drop 52).take 32 },
                      { type := 0x0404, body := ntsReply.drop 88 }],
             mac := [] } ∧
    Ntp.decode withMac =
      some { header := clientHeader,
             exts := [{ type := 0x0104, body := field16.drop 4 },
                      { type := 0x0204, body := field20.drop 4 }],
             mac := mac20 } ∧
    Ntp.decode cryptoNak = some { header := serverHeader, exts := [], mac := [0, 0, 0, 0] } ∧
    Ntp.decode v3WithMac =
      some { header := { clientHeader with version := 3 }, exts := [], mac := mac20 } ∧
    Ntp.decode (clientRequest ++ tail24) =
      some { header := clientHeader, exts := [], mac := tail24 } ∧
    Ntp.decode (clientRequest ++ autokeyAssoc ++ mac20) =
      some { header := clientHeader, exts := [{ type := 0x0102, body := autokeyAssoc.drop 4 }],
             mac := mac20 } ∧
    Ntp.encode { header := serverHeader, exts := [], mac := [] } = serverReply ∧
    Ntp.toUnix 0 0xE5F663A8798EAE2B = some (1649141032, 0x798EAE2B) ∧
    Ntp.fromUnix 1649141032 0x798EAE2B = some (0, 0xE5F663A8798EAE2B) ∧
    Ntp.toUnix 0 (2208988800 * 2 ^ 32) = some (0, 0) ∧
    Ntp.toUnix 0 0xFFFFFFFF00000000 = some (2085978495, 0) ∧
    Ntp.toUnix 0 0x0000000100000000 = some (-2208988799, 0) ∧
    Ntp.toUnix 1 0x0000000100000000 = some (2085978497, 0) ∧
    Ntp.toUnix 1 0 = none ∧
    Ntp.fromUnix 2085978496 0 = none ∧
    Ntp.fromUnix 2085978496 1 = some (1, 1) ∧
    Ntp.toUnix (-1) 0xFFFFFFFF00000000 = some (-2208988801, 0) := by
  sorry

/-- Packets that each break one rule, each after a packet that differs
    from it only there and is accepted:
    - versions 2 and 5, and modes 0, 6 and 7, in the server reply, which
      is accepted;
    - the server reply cut to 47 octets;
    - a version 4 field of Length 12 (less than the 16 of RFC 7822),
      then a field of 28; accepted with a first field of Length 16;
    - a last field of Length 30, not a multiple of 4; accepted with
      Length 32;
    - a field of Length 256 with 32 octets left, a Length that runs past
      the end of the packet (CVE-2014-9750's flaw, at the level of the
      field's own Length); accepted with Length 32;
    - without a MAC, a last field of 16 octets after one of 28 (RFC 7822
      7.5.1.4 asks for 28); accepted the other way round;
    - four octets after the header that are not zero; accepted as four
      zero octets, the crypto-NAK;
    - a field, then four zero octets: the crypto-NAK has no fields;
      accepted without the four octets;
    - a version 3 packet with a field of 28 octets; accepted in version
      4;
    - 21 octets after the header; accepted as the 20-octet MAC. -/
theorem rejects :
    (Ntp.decode serverReply).isSome ∧
    Ntp.decode (0x14 :: serverReply.tail) = none ∧
    Ntp.decode (0x2C :: serverReply.tail) = none ∧
    Ntp.decode (0x20 :: serverReply.tail) = none ∧
    Ntp.decode (0x26 :: serverReply.tail) = none ∧
    Ntp.decode (0x27 :: serverReply.tail) = none ∧
    Ntp.decode (serverReply.take 47) = none ∧
    (Ntp.decode (clientRequest ++ [0x01, 0x04, 0x00, 0x10] ++ List.replicate 12 0x5A ++
      field28)).isSome ∧
    Ntp.decode (clientRequest ++ [0x01, 0x04, 0x00, 0x0C] ++ List.replicate 8 0x5A ++ field28) =
      none ∧
    (Ntp.decode (clientRequest ++ [0x01, 0x04, 0x00, 0x20] ++ List.replicate 28 0x5A)).isSome ∧
    Ntp.decode (clientRequest ++ [0x01, 0x04, 0x00, 0x1E] ++ List.replicate 26 0x5A) = none ∧
    Ntp.decode (clientRequest ++ [0x01, 0x04, 0x01, 0x00] ++ List.replicate 28 0x5A) = none ∧
    (Ntp.decode (clientRequest ++ field16 ++ field28)).isSome ∧
    Ntp.decode (clientRequest ++ field28 ++ field16) = none ∧
    (Ntp.decode cryptoNak).isSome ∧
    Ntp.decode (serverReply ++ [0x00, 0x00, 0x00, 0x01]) = none ∧
    (Ntp.decode (serverReply ++ field28)).isSome ∧
    Ntp.decode (serverReply ++ field28 ++ [0, 0, 0, 0]) = none ∧
    (Ntp.decode (clientRequest ++ field28)).isSome ∧
    Ntp.decode ((0x1B :: clientRequest.tail) ++ field28) = none ∧
    (Ntp.decode (serverReply ++ mac20)).isSome ∧
    Ntp.decode (serverReply ++ mac20 ++ [0x00]) = none := by
  sorry

end Spec
