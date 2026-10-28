/-
  The NTP packet, written from RFC 5905 ("Network Time Protocol Version
  4: Protocol and Algorithms Specification") as RFC 7822 ("NTPv4
  Extension Fields") updates it: the 48-octet header (5905 Figure 8 and
  section 7.3), extension fields (7822 section 3, Figure 14), the MAC,
  and timestamps (5905 section 6).

  Bytes are `List UInt8`, one UDP payload. Every multi-octet field is
  big-endian ("network byte order", RFC 5906 section 10). This file
  uses nothing from the code.
-/

namespace Spec

/-! ## Integers -/

/-- `n` as `w` bytes, most significant first. -/
def beBytes (w n : Nat) : List UInt8 :=
  (List.range w).reverse.map fun i => (n / 256 ^ i % 256).toUInt8

/-- An 8-bit signed integer as its byte, in two's complement. Poll and
    Precision are each an "8-bit signed integer" (RFC 5905 7.3). -/
def signedByte (z : Int) : UInt8 := (z % 256).toNat.toUInt8

/-! ## The header (RFC 5905 Figure 8, section 7.3) -/

/-- The fields of the header, in the order of Figure 8:
    - `leap`, LI: the "2-bit integer warning of an impending leap
      second" (Figure 9);
    - `version`, VN: the "3-bit integer representing the NTP version
      number";
    - `mode`: the "3-bit integer representing the mode" (Figure 10);
    - `stratum`: an "8-bit integer" (Figure 11);
    - `poll` and `precision`: each an "8-bit signed integer", in log2
      seconds;
    - `rootDelay` and `rootDispersion`: each in "NTP short format", 16
      bits of seconds and 16 of fraction (section 6), kept as its 32
      bits;
    - `refId`: the "32-bit code identifying the particular server or
      reference clock", kept as its 32 bits, the first octet most
      significant;
    - the Reference, Origin, Receive and Transmit Timestamps: each in
      "NTP timestamp format", 32 bits of seconds and 32 of fraction
      (section 6), kept as its 64 bits. -/
structure Header where
  leap : Nat
  version : Nat
  mode : Nat
  stratum : Nat
  poll : Int
  precision : Int
  rootDelay : Nat
  rootDispersion : Nat
  refId : Nat
  reference : Nat
  origin : Nat
  receive : Nat
  transmit : Nat
  deriving DecidableEq, Repr

/-- The header as its 48 octets: LI, VN and Mode packed into the first
    octet, two bits, three bits and three bits from the most significant
    end; then Stratum, Poll and Precision; then Root Delay, Root
    Dispersion and Reference ID, 32 bits each; then the four 64-bit
    timestamps. -/
def headerBytes (h : Header) : List UInt8 :=
  [(h.leap * 64 + h.version * 8 + h.mode).toUInt8, h.stratum.toUInt8,
    signedByte h.poll, signedByte h.precision] ++
  beBytes 4 h.rootDelay ++ beBytes 4 h.rootDispersion ++ beBytes 4 h.refId ++
  beBytes 8 h.reference ++ beBytes 8 h.origin ++ beBytes 8 h.receive ++ beBytes 8 h.transmit

/-- The headers this reader accepts:
    - every field small enough for its bits;
    - version 3 or 4 (VN is "currently 4"; version 3 is RFC 1305, with
      which the header is "backwards compatible", 5905 section 7.3);
    - mode 1 to 5. Mode 0 is "reserved", mode 6 is "NTP control
      message" and mode 7 is "reserved for private use" (Figure 10):
      their packets are not this format. -/
def HeaderValid (h : Header) : Prop :=
  h.leap < 4 ∧ (h.version = 3 ∨ h.version = 4) ∧ 1 ≤ h.mode ∧ h.mode ≤ 5 ∧
  h.stratum < 256 ∧ -128 ≤ h.poll ∧ h.poll < 128 ∧ -128 ≤ h.precision ∧ h.precision < 128 ∧
  h.rootDelay < 2 ^ 32 ∧ h.rootDispersion < 2 ^ 32 ∧ h.refId < 2 ^ 32 ∧
  h.reference < 2 ^ 64 ∧ h.origin < 2 ^ 64 ∧ h.receive < 2 ^ 64 ∧ h.transmit < 2 ^ 64

/-! ## Extension fields (RFC 7822 section 3, Figure 14) -/

/-- An extension field: its Field Type, and the octets after its Length
    field, which are its Value and its Padding. Where the Value ends and
    the Padding starts is "specific to the defined function", so they
    are kept together. -/
structure ExtField where
  type : Nat
  body : List UInt8
  deriving DecidableEq, Repr

/-- The Length field: "the length of the entire extension field in
    octets, including the Padding field", so the four octets of Field
    Type and Length as well. -/
def ExtField.length (e : ExtField) : Nat := e.body.length + 4

/-- The field as its octets: the 16-bit Field Type, the 16-bit Length,
    then the Value and Padding. -/
def extBytes (e : ExtField) : List UInt8 :=
  beBytes 2 e.type ++ beBytes 2 e.length ++ e.body

/-- An extension field this reader accepts: "All extension fields are
    zero-padded to a word (four octets) boundary", so the Length is a
    multiple of 4; "the minimum field length containing required fields
    is four words (16 octets)"; and "the maximum field length cannot be
    longer than 65532 octets, due to the maximum size of the Length
    field", which with the first rule is a Length below 2^16. -/
def ExtValid (e : ExtField) : Prop :=
  e.type < 2 ^ 16 ∧ 16 ≤ e.length ∧ e.length % 4 = 0 ∧ e.length < 2 ^ 16

/-! ## The packet -/

/-- A packet: the header, the extension fields in order, and the MAC,
    which is empty when the packet has none. -/
structure Packet where
  header : Header
  exts : List ExtField
  mac : List UInt8
  deriving DecidableEq, Repr

/-- The packet as its octets: "The NTP packet header shown in Figure 8
    has 12 words followed by optional extension fields and finally an
    optional message authentication code (MAC)" (5905 7.3). -/
def packetBytes (p : Packet) : List UInt8 :=
  headerBytes p.header ++ p.exts.flatMap extBytes ++ p.mac

/-- The MACs this reader accepts:
    - none;
    - a 20- or 24-octet MAC: the 32-bit Key Identifier, then a 128-bit
      digest (5905 7.3) or a 160-bit one. RFC 7822 7.5.1.3: "A MAC MUST
      NOT be longer than 24 octets if there is no extension field
      present"; this reader takes no longer MAC with extension fields
      either, since a MAC length agreed by other means is not in the
      packet;
    - the crypto-NAK, "a MAC consisting of four octets of zeros" (5905
      section 9.2), "the key identifier with value zero" (5905 A.5), in a
      packet with no extension field. -/
def MacValid (exts : List ExtField) (mac : List UInt8) : Prop :=
  mac = [] ∨ mac.length = 20 ∨ mac.length = 24 ∨ (mac = [0, 0, 0, 0] ∧ exts = [])

/-- The packets this reader accepts:
    - the header is valid;
    - each extension field is valid;
    - a version 3 packet has no extension fields: "In NTPv4, one or more
      extension fields can be inserted after the header and before the
      MAC, if a MAC is present" (7822 section 3), and RFC 1305 has a
      header and an optional authenticator only;
    - the MAC is one of `MacValid`;
    - without a MAC, the last extension field is at least 28 octets:
      "If the packet includes a single extension field, the length of
      the extension field MUST be at least 7 words, i.e., at least 28
      octets. If the packet includes more than one extension field, the
      length of the last extension field MUST be at least 28 octets"
      (7822 7.5.1.4).

    These rules make the octets after the header read one way only: see
    `SPEC.md`. -/
def Valid (p : Packet) : Prop :=
  HeaderValid p.header ∧
  (∀ e ∈ p.exts, ExtValid e) ∧
  (p.header.version = 3 → p.exts = []) ∧
  MacValid p.exts p.mac ∧
  (p.mac = [] → ∀ e ∈ p.exts.getLast?, 28 ≤ e.length)

/-! ## Timestamps (RFC 5905 section 6) -/

/-- Seconds from the prime epoch, 0 h 1 January 1900 UTC, to the Unix
    epoch: "1 Jan 1970 ... 0 ... 2,208,988,800 First day UNIX" (Figure 4:
    era 0, era offset 2,208,988,800). -/
def unixEpoch : Nat := 2208988800

end Spec
