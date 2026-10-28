import Ntp

/-!
  Fixed-width fields: `take?`, big-endian integers, `readBE` and
  `writeBE`, against `Spec.beBytes`.
-/

namespace NtpProofs

open Spec Ntp

theorem take?_eq (w : Nat) (b c r : List UInt8) :
    take? w b = some (c, r) ↔ c.length = w ∧ b = c ++ r := by
  unfold take?
  dsimp only
  constructor
  · intro h
    split at h
    · rename_i hl
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨hl, (List.take_append_drop w b).symm⟩
    · exact absurd h (by simp)
  · rintro ⟨hl, rfl⟩
    subst hl
    simp

theorem take?_append (w : Nat) (c r : List UInt8) (h : c.length = w) :
    take? w (c ++ r) = some (c, r) :=
  (take?_eq _ _ _ _).mpr ⟨h, rfl⟩

theorem take?_none (w : Nat) (b : List UInt8) (h : b.length < w) : take? w b = none := by
  unfold take?
  dsimp only
  split
  · rename_i h'
    rw [List.length_take] at h'
    omega
  · rfl

theorem beBytes_length (w n : Nat) : (beBytes w n).length = w := by
  simp [beBytes]

theorem foldl_be (acc : Nat) (bs : List UInt8) :
    bs.foldl (fun n b => n * 256 + b.toNat) acc =
      acc * 256 ^ bs.length + bs.foldl (fun n b => n * 256 + b.toNat) 0 := by
  induction bs generalizing acc with
  | nil => simp
  | cons b bs ih =>
    simp only [List.foldl_cons, List.length_cons]
    rw [ih, ih (0 * 256 + b.toNat)]
    simp [Nat.pow_succ, Nat.mul_add, Nat.mul_assoc, Nat.add_assoc, Nat.mul_comm]

theorem bigEndian_cons (b : UInt8) (bs : List UInt8) :
    bigEndian (b :: bs) = b.toNat * 256 ^ bs.length + bigEndian bs := by
  unfold bigEndian
  rw [List.foldl_cons, foldl_be]
  simp

theorem bigEndian_lt (bs : List UInt8) : bigEndian bs < 256 ^ bs.length := by
  induction bs with
  | nil => simp [bigEndian]
  | cons b bs ih =>
    rw [bigEndian_cons, List.length_cons, Nat.pow_succ]
    have hb : b.toNat ≤ 255 := by have := b.toNat_lt; omega
    have h1 : b.toNat * 256 ^ bs.length ≤ 255 * 256 ^ bs.length := Nat.mul_le_mul_right _ hb
    omega

theorem beBytes_succ (w n : Nat) :
    beBytes (w + 1) n = (n / 256 ^ w % 256).toUInt8 :: beBytes w n := by
  simp [beBytes, List.range_succ]

theorem toNat_toUInt8 (n : Nat) (h : n < 256) : n.toUInt8.toNat = n := by
  simp [Nat.toUInt8, Nat.mod_eq_of_lt h]

theorem bigEndian_beBytes (w n : Nat) : bigEndian (beBytes w n) = n % 256 ^ w := by
  induction w with
  | zero => simp [beBytes, bigEndian, Nat.mod_one]
  | succ w ih =>
    rw [beBytes_succ, bigEndian_cons, ih, beBytes_length,
      toNat_toUInt8 _ (Nat.mod_lt _ (by decide)), Nat.pow_succ, Nat.mod_mul,
      Nat.mul_comm (n / 256 ^ w % 256)]
    omega

theorem bigEndian_beBytes_of_lt (w n : Nat) (h : n < 256 ^ w) : bigEndian (beBytes w n) = n := by
  rw [bigEndian_beBytes, Nat.mod_eq_of_lt h]

theorem beBytes_add (w a n : Nat) : beBytes w (a * 256 ^ w + n) = beBytes w n := by
  unfold beBytes
  apply List.map_congr_left
  intro i hi
  simp only [List.mem_reverse, List.mem_range] at hi
  congr 1
  obtain ⟨d, rfl⟩ : ∃ d, w = i + d + 1 := ⟨w - i - 1, by omega⟩
  rw [show i + d + 1 = i + (d + 1) by omega, Nat.pow_add, ← Nat.mul_assoc,
    Nat.mul_right_comm a, Nat.add_comm, Nat.add_mul_div_right _ _ (Nat.pow_pos (by decide)),
    Nat.pow_succ, ← Nat.mul_assoc, Nat.add_mul_mod_self_right]

theorem beBytes_bigEndian (c : List UInt8) : beBytes c.length (bigEndian c) = c := by
  induction c with
  | nil => rfl
  | cons b c ih =>
    rw [List.length_cons, beBytes_succ, bigEndian_cons]
    have hc := bigEndian_lt c
    have hdiv : (b.toNat * 256 ^ c.length + bigEndian c) / 256 ^ c.length = b.toNat := by
      rw [Nat.add_comm, Nat.add_mul_div_right _ _ (Nat.pow_pos (by decide)),
        Nat.div_eq_of_lt hc, Nat.zero_add]
    rw [hdiv, Nat.mod_eq_of_lt b.toNat_lt, beBytes_add, ih]
    simp

theorem readBE_iff (w : Nat) (b : List UInt8) (n : Nat) (r : List UInt8) :
    readBE w b = some (n, r) ↔ n < 256 ^ w ∧ b = beBytes w n ++ r := by
  unfold readBE
  constructor
  · intro h
    simp only [Option.map_eq_some_iff, Prod.exists] at h
    obtain ⟨c, r', hc, he⟩ := h
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    obtain ⟨hl, rfl⟩ := (take?_eq _ _ _ _).mp hc
    subst hl
    exact ⟨bigEndian_lt c, by rw [beBytes_bigEndian]⟩
  · rintro ⟨hn, rfl⟩
    rw [take?_append w _ r (beBytes_length _ _)]
    simp [bigEndian_beBytes_of_lt _ _ hn]

theorem readBE_append (w n : Nat) (r : List UInt8) (hn : n < 256 ^ w) :
    readBE w (beBytes w n ++ r) = some (n, r) :=
  (readBE_iff _ _ _ _).mpr ⟨hn, rfl⟩

/-- Reading `w` octets from `w` written ones gives the number modulo
    `256 ^ w`, whatever it was. -/
theorem readBE_append_mod (w n : Nat) (r : List UInt8) :
    readBE w (beBytes w n ++ r) = some (n % 256 ^ w, r) := by
  unfold readBE
  rw [take?_append w _ r (beBytes_length _ _)]
  simp [bigEndian_beBytes]

theorem guard_some (p : Prop) [Decidable p] (u : Unit) :
    (guard p : Option Unit) = some u ↔ p := by
  unfold guard
  split <;> simp_all [failure, pure]

theorem beBytes_one (a : Nat) (h : a < 256) : beBytes 1 a = [a.toUInt8] := by
  simp [beBytes, Nat.mod_eq_of_lt h]

theorem readBE_one (a : UInt8) (r : List UInt8) : readBE 1 (a :: r) = some (a.toNat, r) := by
  have := readBE_append 1 a.toNat r (by simpa using a.toNat_lt)
  rw [beBytes_one _ a.toNat_lt] at this
  simpa using this

theorem beBytes_snoc (w n : Nat) :
    beBytes (w + 1) n = beBytes w (n / 256) ++ [(n % 256).toUInt8] := by
  induction w generalizing n with
  | zero => simp [beBytes]
  | succ w ih =>
    rw [beBytes_succ, ih, beBytes_succ, Nat.div_div_eq_div_mul, Nat.pow_succ,
      Nat.mul_comm (256 ^ w) 256]
    rfl

theorem writeBE_eq (w n : Nat) : writeBE w n = beBytes w n := by
  induction w generalizing n with
  | zero => rfl
  | succ w ih => rw [writeBE, ih, beBytes_snoc]

end NtpProofs
