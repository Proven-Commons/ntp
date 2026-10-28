import Proofs.Bytes

/-!
  The header reader against `Spec.headerBytes` and `Spec.HeaderValid`.
-/

namespace NtpProofs

open Spec Ntp

theorem headerBytes_length (h : Header) : (headerBytes h).length = 48 := by
  simp [headerBytes, beBytes_length]

/-- The first octet gives back LI, VN and Mode. -/
theorem lvm_bits (a : Nat) : a / 64 * 64 + a / 8 % 8 * 8 + a % 8 = a := by
  omega

theorem signedByte_toSigned (n : Nat) (h : n < 256) : signedByte (toSigned n) = n.toUInt8 := by
  unfold signedByte toSigned
  congr 1
  split <;> omega

theorem toSigned_signedByte (z : Int) (h1 : -128 ≤ z) (h2 : z < 128) :
    toSigned (signedByte z).toNat = z := by
  unfold signedByte toSigned
  rw [toNat_toUInt8 _ (by omega)]
  split <;> omega

theorem toSigned_range (n : Nat) (h : n < 256) : -128 ≤ toSigned n ∧ toSigned n < 128 := by
  unfold toSigned
  split <;> omega

theorem readHeader_some (b : List UInt8) (h : Header) (t : List UInt8)
    (H : readHeader b = some (h, t)) : HeaderValid h ∧ b = headerBytes h ++ t := by
  unfold readHeader at H
  simp only [bind, Option.bind_eq_some_iff, Prod.exists, readBE_iff, guard_some, pure,
    Option.some.injEq, Prod.mk.injEq, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq,
    decide_eq_true_eq, Nat.reducePow, exists_and_left, exists_const] at H
  obtain ⟨lvm, r, ⟨hlvm, rfl⟩, ⟨⟨hver, hm1⟩, hm2⟩, st, r, ⟨hst, rfl⟩, po, r, ⟨hpo, rfl⟩,
    pr, r, ⟨hpr, rfl⟩, rd, r, ⟨hrd, rfl⟩, rs, r, ⟨hrs, rfl⟩, ri, r, ⟨hri, rfl⟩,
    rt, r, ⟨hrt, rfl⟩, ot, r, ⟨hot, rfl⟩, vt, r, ⟨hvt, rfl⟩, xt, r, ⟨hxt, rfl⟩, rfl, rfl⟩ := H
  have hp := toSigned_range po hpo
  have hq := toSigned_range pr hpr
  refine ⟨?_, ?_⟩
  · simp only [HeaderValid, Nat.reducePow]
    refine ⟨by omega, hver, hm1, hm2, hst, hp.1, hp.2, hq.1, hq.2, hrd, hrs, hri, hrt, hot, hvt,
      hxt⟩
  · simp only [headerBytes, List.append_assoc, beBytes_one _ hlvm, beBytes_one _ hst,
      beBytes_one _ hpo, beBytes_one _ hpr, lvm_bits lvm, signedByte_toSigned _ hpo,
      signedByte_toSigned _ hpr, List.cons_append, List.nil_append]

theorem readBE_one' (a : UInt8) (l r : List UInt8) :
    readBE 1 ((a :: l) ++ r) = some (a.toNat, l ++ r) :=
  readBE_one a (l ++ r)

theorem readHeader_bytes (h : Header) (hv : HeaderValid h) (rest : List UInt8) :
    readHeader (headerBytes h ++ rest) = some (h, rest) := by
  have hv' := hv
  simp only [HeaderValid] at hv'
  obtain ⟨hl, hver, hm1, hm2, hst, hp1, hp2, hq1, hq2, hrd, hrs, hri, hrt, hot, hvt, hxt⟩ := hv'
  have b4 : ∀ n, n < 2 ^ 32 → n < 256 ^ 4 := fun n h => by simpa using h
  have b8 : ∀ n, n < 2 ^ 64 → n < 256 ^ 8 := fun n h => by simpa using h
  have hlvm : h.leap * 64 + h.version * 8 + h.mode < 256 := by omega
  unfold readHeader headerBytes
  simp only [bind, List.append_assoc, List.cons_append, List.nil_append, readBE_one,
    Option.bind_some,
    readBE_append 4 _ _ (b4 _ hrd), readBE_append 4 _ _ (b4 _ hrs), readBE_append 4 _ _ (b4 _ hri),
    readBE_append 8 _ _ (b8 _ hrt), readBE_append 8 _ _ (b8 _ hot), readBE_append 8 _ _ (b8 _ hvt),
    readBE_append 8 _ _ (b8 _ hxt), toNat_toUInt8 _ hlvm, toNat_toUInt8 _ hst,
    toSigned_signedByte _ hp1 hp2, toSigned_signedByte _ hq1 hq2]
  have e1 : (h.leap * 64 + h.version * 8 + h.mode) / 8 % 8 = h.version := by omega
  have e2 : (h.leap * 64 + h.version * 8 + h.mode) % 8 = h.mode := by omega
  have e3 : (h.leap * 64 + h.version * 8 + h.mode) / 64 = h.leap := by omega
  have hg : ((h.version == 3 || h.version == 4) && decide (1 ≤ h.mode) && decide (h.mode ≤ 5))
      = true := by
    simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq]
    exact ⟨⟨hver, hm1⟩, hm2⟩
  simp only [e1, e2, e3, hg, guard, ite_true, Option.bind_some, pure]

theorem readHeader_iff (b : List UInt8) (h : Header) (t : List UInt8) :
    readHeader b = some (h, t) ↔ HeaderValid h ∧ b = headerBytes h ++ t := by
  constructor
  · exact readHeader_some b h t
  · rintro ⟨hv, rfl⟩
    exact readHeader_bytes h hv t

end NtpProofs
