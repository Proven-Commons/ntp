/-
  NTP timestamps and Unix time. A timestamp is 32 bits of seconds and 32
  bits of fraction since the start of its era (RFC 5905 section 6); the
  era is not in the packet, so it is an argument here.
-/

namespace Ntp

/-- The Unix time of the 64-bit timestamp `raw` in era `era`, as whole
    seconds and a fraction in units of 2^-32 seconds; `none` for the raw
    value 0, which means unknown, and for a value of more than 64 bits.
    The seconds are `era * 2^32` plus the seconds field, less the
    2,208,988,800 seconds from 1900 to 1970. -/
def toUnix (era : Int) (raw : Nat) : Option (Int × Nat) :=
  if raw = 0 ∨ 18446744073709551616 ≤ raw then none
  else some (era * 4294967296 + (raw / 4294967296 : Nat) - 2208988800, raw % 4294967296)

/-- The era and the 64-bit timestamp of a Unix time, given as whole
    seconds and a fraction in units of 2^-32 seconds; `none` when the
    fraction is not below 2^32, and at the first instant of an era,
    whose timestamp would be 0, the value that means unknown. -/
def fromUnix (seconds : Int) (fraction : Nat) : Option (Int × Nat) :=
  if 4294967296 ≤ fraction then none
  else
    let s := seconds + 2208988800
    let raw := (s % 4294967296).toNat * 4294967296 + fraction
    if raw = 0 then none else some (s / 4294967296, raw)

end Ntp
