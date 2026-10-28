/-
  Command line front end.

    ntp serve

  answers requests on standard input, one per line, for the
  differential tests. Octets are lower-case hex digits, two per octet,
  and an empty list of octets is written `-`. Numbers are decimal, and
  a signed one may start with `-`.

    decode HEX          prints  OK and the packet, or FAIL      (decode)
    encode PACKET       prints  OK and the hex of the octets that
                                `encode` writes for the packet, when
                                `decode` reads the packet back from
                                them, or FAIL                   (encode, decode)
    unix ERA RAW        prints  OK, the seconds and the fraction of
                                the Unix time of the timestamp RAW in
                                era ERA, or FAIL                (toUnix)
    fromunix S F        prints  OK, the era and the timestamp of the
                                Unix time S + F / 2^32 seconds,
                                or FAIL                         (fromUnix)

  A packet is written as 15 fields, separated by spaces:
    - LI, VN, Mode, Stratum, Poll, Precision, Root Delay, Root
      Dispersion, Reference ID, and the Reference, Origin, Receive and
      Transmit Timestamps, in decimal: Poll and Precision as signed
      numbers, the others as the unsigned number their bits hold;
    - the extension fields: `-` when there are none, or else each one
      as its Field Type in decimal, `:` and the hex of its Value and
      Padding (`-` when empty), separated by commas;
    - the hex of the MAC, or `-` when there is none.
  `decode` prints a packet this way, and `encode` reads one. By
  `Spec.decode_encode`, `encode` prints OK exactly when the packet it
  is given is valid.

  A malformed request prints `error`: an unknown operation, the wrong
  number of fields, hex digits that are not in pairs or not lower case,
  or a number that is not decimal. A request line may end in LF or
  CR LF.

  Every answer comes from the proved functions in `Ntp/`. The hex
  coding, the output and the request handling here are covered by the
  tests, not by a proof.
-/

import Ntp

open Ntp Spec

def hexValue (c : Char) : Option Nat :=
  if '0' ≤ c ∧ c ≤ '9' then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c ∧ c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
  else none

/-- Octets from hex digits in pairs. Tail recursive, so that long
    inputs do not use the stack. -/
def hexBytes (cs : List Char) (acc : Array UInt8) : Option (Array UInt8) :=
  match cs with
  | [] => some acc
  | a :: b :: rest =>
    match hexValue a, hexValue b with
    | some hi, some lo => hexBytes rest (acc.push (hi * 16 + lo).toUInt8)
    | _, _ => none
  | [_] => none

/-- The octets a field gives: `-` for none, else hex digits in pairs. -/
def fromHex (f : String) : Option (List UInt8) :=
  if f = "-" then some [] else if f.isEmpty then none else (hexBytes f.toList #[]).map (·.toList)

def hexDigit (n : Nat) : Char :=
  if n < 10 then Char.ofNat ('0'.toNat + n) else Char.ofNat ('a'.toNat + n - 10)

/-- A field for a list of octets: `-` when it is empty. -/
def toHex (bs : List UInt8) : String :=
  if bs.isEmpty then "-"
  else String.ofList (bs.flatMap fun b => [hexDigit (b.toNat / 16), hexDigit (b.toNat % 16)])

/-- A decimal number, without sign or leading `+`. -/
def decimal (s : String) : Option Nat :=
  if !s.isEmpty && s.all Char.isDigit then s.toNat? else none

/-- A decimal number, with `-` in front when it is negative. -/
def integer (s : String) : Option Int :=
  match s.toList with
  | '-' :: cs => (decimal (String.ofList cs)).map fun n => -(n : Int)
  | _ => (decimal s).map fun n => (n : Int)

def showField (e : ExtField) : String := s!"{e.type}:{toHex e.body}"

def showPacket (p : Packet) : String :=
  let h := p.header
  let exts := if p.exts.isEmpty then "-" else ",".intercalate (p.exts.map showField)
  " ".intercalate [toString h.leap, toString h.version, toString h.mode, toString h.stratum,
    toString h.poll, toString h.precision, toString h.rootDelay, toString h.rootDispersion,
    toString h.refId, toString h.reference, toString h.origin, toString h.receive,
    toString h.transmit, exts, toHex p.mac]

def readField (s : String) : Option ExtField :=
  match s.splitOn ":" with
  | [t, b] => do
    let type ← decimal t
    let body ← fromHex b
    pure { type, body }
  | _ => none

def readFieldList (s : String) : Option (List ExtField) :=
  if s = "-" then some [] else (s.splitOn ",").mapM readField

/-- A packet written as `showPacket` writes one. -/
def readPacket : List String → Option Packet
  | [l, v, m, st, po, pr, rd, rs, ri, rt, ot, vt, xt, es, mac] => do
    let header : Header :=
      { leap := ← decimal l, version := ← decimal v, mode := ← decimal m,
        stratum := ← decimal st, poll := ← integer po, precision := ← integer pr,
        rootDelay := ← decimal rd, rootDispersion := ← decimal rs, refId := ← decimal ri,
        reference := ← decimal rt, origin := ← decimal ot, receive := ← decimal vt,
        transmit := ← decimal xt }
    let exts ← readFieldList es
    let mac ← fromHex mac
    pure { header, exts, mac }
  | _ => none

/-- The answer to one request line, or `none` when it is malformed. -/
def request (line : String) : Option String :=
  match line.splitOn " " with
  | ["decode", h] => do
    let b ← fromHex h
    pure (match decode b with
      | some p => s!"OK {showPacket p}"
      | none => "FAIL")
  | "encode" :: fields => do
    let p ← readPacket fields
    let b := encode p
    pure (if decode b = some p then s!"OK {toHex b}" else "FAIL")
  | ["unix", e, r] => do
    let era ← integer e
    let raw ← decimal r
    pure (match toUnix era raw with
      | some (s, f) => s!"OK {s} {f}"
      | none => "FAIL")
  | ["fromunix", s, f] => do
    let seconds ← integer s
    let fraction ← decimal f
    pure (match fromUnix seconds fraction with
      | some (era, raw) => s!"OK {era} {raw}"
      | none => "FAIL")
  | _ => none

/-- A request line without its line ending, LF or CR LF. -/
def chomp (line : String) : String :=
  let cs := line.toList
  if cs.getLast? = some '\n' then
    let cs := cs.dropLast
    String.ofList (if cs.getLast? = some '\r' then cs.dropLast else cs)
  else line

def serve : IO Unit := do
  let stdin ← IO.getStdin
  let stdout ← IO.getStdout
  repeat
    let line ← stdin.getLine
    if line.isEmpty then break
    stdout.putStrLn ((request (chomp line)).getD "error")
    stdout.flush

def usage : String := "usage: ntp serve"

def main (args : List String) : IO UInt32 := do
  match args with
  | ["serve"] => serve; return 0
  | _ => IO.eprintln usage; return 2
