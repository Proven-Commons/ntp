/-
  Reading and writing the NTP packet: the 48-octet header of RFC 5905,
  then extension fields (RFC 7822) and a MAC. The structures the reader
  gives back are those of `Ntp/Spec/Defs.lean`; the functions here are the
  code under proof, and share nothing else with the specification.
-/

import Ntp.Spec.Defs

namespace Ntp

open Ntp.Spec (Header ExtField Packet)

/-! ## Octets -/

/-- Splits off the first `w` octets, if there are that many. Looks at
    no more than those `w`. -/
def take? (w : Nat) (b : List UInt8) : Option (List UInt8 × List UInt8) :=
  let c := b.take w
  if c.length = w then some (c, b.drop w) else none

/-- The octets as a big-endian unsigned integer. -/
def bigEndian (bs : List UInt8) : Nat :=
  bs.foldl (fun n b => n * 256 + b.toNat) 0

/-- A `w`-octet big-endian integer at the start of the input, and the
    rest. -/
def readBE (w : Nat) (b : List UInt8) : Option (Nat × List UInt8) :=
  (take? w b).map fun (c, r) => (bigEndian c, r)

/-- `n` as `w` octets, most significant first. -/
def writeBE : Nat → Nat → List UInt8
  | 0, _ => []
  | w + 1, n => writeBE w (n / 256) ++ [(n % 256).toUInt8]

/-- An octet read as an 8-bit two's complement integer. -/
def toSigned (n : Nat) : Int :=
  if n < 128 then n else (n : Int) - 256

/-- An 8-bit two's complement integer as an octet. -/
def ofSigned (z : Int) : Nat :=
  if z < 0 then (z + 256).toNat else z.toNat

/-- Whether the list has more than `n` elements. Looks at no more than
    `n + 1` of them. -/
def longer : Nat → List UInt8 → Bool
  | _, [] => false
  | 0, _ :: _ => true
  | n + 1, _ :: t => longer n t

/-! ## Reading -/

/-- The 48-octet header at the start of the input, and the rest. The
    first octet holds LI in its top two bits, then VN in three, then
    Mode in three. Only versions 3 and 4 and modes 1 to 5 are read. -/
def readHeader (b : List UInt8) : Option (Header × List UInt8) := do
  let (lvm, r) ← readBE 1 b
  let version := lvm / 8 % 8
  let mode := lvm % 8
  guard ((version == 3 || version == 4) && 1 ≤ mode && mode ≤ 5)
  let (stratum, r) ← readBE 1 r
  let (poll, r) ← readBE 1 r
  let (precision, r) ← readBE 1 r
  let (rootDelay, r) ← readBE 4 r
  let (rootDispersion, r) ← readBE 4 r
  let (refId, r) ← readBE 4 r
  let (reference, r) ← readBE 8 r
  let (origin, r) ← readBE 8 r
  let (receive, r) ← readBE 8 r
  let (transmit, r) ← readBE 8 r
  pure ({ leap := lvm / 64, version, mode, stratum, poll := toSigned poll,
          precision := toSigned precision, rootDelay, rootDispersion, refId, reference,
          origin, receive, transmit }, r)

/-- Whether what is left after the header and the extension fields is
    no MAC, or a MAC of a 4-octet key identifier and a 16- or 20-octet
    digest. -/
def macLength (t : List UInt8) : Bool :=
  t.length == 0 || t.length == 20 || t.length == 24

/-- The extension fields of a version 4 packet and its MAC, from the
    octets after the header. While more than 24 octets are left, they
    start with a field: a 16-bit Field Type, a 16-bit Length that counts
    the whole field, at least 16 and a multiple of 4, then the rest of
    the field. What is left after the last field is the MAC. `fuel`
    bounds the number of fields. -/
def readFields : Nat → List UInt8 → Option (List ExtField × List UInt8)
  | 0, _ => none
  | fuel + 1, t =>
    if longer 24 t then do
      let (type, r) ← readBE 2 t
      let (len, r) ← readBE 2 r
      guard (16 ≤ len && len % 4 == 0)
      let (body, r) ← take? (len - 4) r
      let (fields, mac) ← readFields fuel r
      pure ({ type, body } :: fields, mac)
    else if macLength t then some ([], t) else none

/-- The extension fields and the MAC after the header. Four zero octets
    are a crypto-NAK. Otherwise a version 4 packet has fields and then a
    MAC, and a version 3 packet a MAC only. -/
def readTail (version : Nat) (t : List UInt8) : Option (List ExtField × List UInt8) :=
  if t = [0, 0, 0, 0] then some ([], t)
  else if version = 4 then readFields (t.length + 1) t
  else if macLength t then some ([], t)
  else none

/-- The packet in one UDP payload, or `none` when the payload is not a
    packet this reader accepts. -/
def decode (b : List UInt8) : Option Packet := do
  let (header, t) ← readHeader b
  let (exts, mac) ← readTail header.version t
  pure { header, exts, mac }

/-! ## Writing -/

/-- An extension field as its octets. -/
def writeField (e : ExtField) : List UInt8 :=
  writeBE 2 e.type ++ writeBE 2 (e.body.length + 4) ++ e.body

/-- A packet as its octets. -/
def encode (p : Packet) : List UInt8 :=
  let h := p.header
  writeBE 1 (h.leap * 64 + h.version * 8 + h.mode) ++ writeBE 1 h.stratum ++
  writeBE 1 (ofSigned h.poll) ++ writeBE 1 (ofSigned h.precision) ++
  writeBE 4 h.rootDelay ++ writeBE 4 h.rootDispersion ++ writeBE 4 h.refId ++
  writeBE 8 h.reference ++ writeBE 8 h.origin ++ writeBE 8 h.receive ++ writeBE 8 h.transmit ++
  p.exts.flatMap writeField ++ p.mac

end Ntp
