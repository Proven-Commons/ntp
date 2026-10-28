import Ntp

/-!
  `toUnix` and `fromUnix`.
-/

namespace NtpProofs

open Spec Ntp

theorem toUnix_zero (era : Int) : toUnix era 0 = none := by
  simp [toUnix]

theorem toUnix_spec (era : Int) (raw : Nat) (s : Int) (f : Nat) :
    toUnix era raw = some (s, f) ↔
      raw ≠ 0 ∧ raw < 2 ^ 64 ∧ f < 2 ^ 32 ∧
        s * 2 ^ 32 + f = era * 2 ^ 64 + raw - unixEpoch * 2 ^ 32 := by
  unfold toUnix unixEpoch
  simp only [Nat.reducePow, Int.reducePow]
  split
  · rename_i h
    simp only [reduceCtorEq, false_iff]
    omega
  · rename_i h
    simp only [Option.some.injEq, Prod.mk.injEq]
    omega

theorem fromUnix_toUnix (era : Int) (raw : Nat) (s : Int) (f : Nat)
    (h : toUnix era raw = some (s, f)) : fromUnix s f = some (era, raw) := by
  unfold toUnix at h
  split at h
  · simp at h
  · rename_i hr
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    unfold fromUnix
    rw [ite_eq_right (by omega)]
    dsimp only
    rw [ite_eq_right (by omega)]
    simp only [Option.some.injEq, Prod.mk.injEq]
    omega

theorem toUnix_fromUnix (s : Int) (f : Nat) (era : Int) (raw : Nat)
    (h : fromUnix s f = some (era, raw)) : toUnix era raw = some (s, f) := by
  unfold fromUnix at h
  split at h
  · simp at h
  · rename_i hf
    dsimp only at h
    split at h
    · simp at h
    · rename_i hr
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      unfold toUnix
      rw [ite_eq_right (by omega)]
      simp only [Option.some.injEq, Prod.mk.injEq]
      omega

end NtpProofs
