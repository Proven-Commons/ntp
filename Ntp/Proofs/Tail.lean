import Ntp.Proofs.Bytes

/-!
  The octets after the header: extension fields and the MAC, against
  `Ntp.Spec.extBytes`, `Ntp.Spec.ExtValid` and `Ntp.Spec.MacValid`.
-/

namespace NtpProofs

open Ntp.Spec Ntp

theorem longer_iff (n : Nat) (t : List UInt8) : longer n t = true ↔ n < t.length := by
  induction t generalizing n with
  | nil => simp [longer]
  | cons x t ih =>
    cases n with
    | zero => simp [longer]
    | succ n => simp [longer, ih]

theorem macLength_iff (t : List UInt8) :
    macLength t = true ↔ t.length = 0 ∨ t.length = 20 ∨ t.length = 24 := by
  simp [macLength, or_assoc]

theorem extBytes_length (e : ExtField) : (extBytes e).length = e.length := by
  simp [extBytes, beBytes_length, ExtField.length]
  omega

theorem flatMap_extBytes_length (es : List ExtField) (h : ∀ e ∈ es, ExtValid e) :
    16 * es.length ≤ (es.flatMap extBytes).length := by
  induction es with
  | nil => simp
  | cons e es ih =>
    simp only [List.flatMap_cons, List.length_append, List.length_cons, extBytes_length]
    have he := (h e (by simp)).2.1
    have := ih (fun x hx => h x (by simp [hx]))
    omega

/-- What `readFields` gives back: valid fields, then a MAC of 0, 20 or
    24 octets, with a last field of at least 28 octets when there is no
    MAC, and the fields and the MAC are the octets it read. -/
theorem readFields_some (fuel : Nat) (t : List UInt8) (es : List ExtField) (mac : List UInt8)
    (H : readFields fuel t = some (es, mac)) :
    (∀ e ∈ es, ExtValid e) ∧ (mac = [] ∨ mac.length = 20 ∨ mac.length = 24) ∧
      (mac = [] → ∀ e ∈ es.getLast?, 28 ≤ e.length) ∧ t = es.flatMap extBytes ++ mac := by
  induction fuel generalizing t es mac with
  | zero => simp [readFields] at H
  | succ fuel ih =>
    unfold readFields at H
    split at H
    · rename_i hlong
      simp only [bind, Option.bind_eq_some_iff, Prod.exists, readBE_iff, guard_some, take?_eq,
        pure, Option.some.injEq, Prod.mk.injEq, Bool.and_eq_true, beq_iff_eq,
        decide_eq_true_eq, Nat.reducePow, exists_and_left, exists_const] at H
      obtain ⟨type, r, ⟨htype, rfl⟩, len, r, ⟨hlen, rfl⟩, ⟨h16, h4⟩, body, r, ⟨hbody, rfl⟩,
        fields, mac', hrec, rfl, rfl⟩ := H
      obtain ⟨hv, hmac, hlast, rfl⟩ := ih _ _ _ hrec
      have hel : ({ type, body } : ExtField).length = len := by
        simp only [ExtField.length]; omega
      refine ⟨?_, hmac, ?_, ?_⟩
      · intro e he
        simp only [List.mem_cons] at he
        rcases he with rfl | he
        · exact ⟨htype, by omega, by omega, by omega⟩
        · exact hv e he
      · intro hm e he
        cases fields with
        | nil =>
          subst hm
          simp only [List.getLast?_singleton, Option.mem_def, Option.some.injEq] at he
          subst he
          rw [longer_iff] at hlong
          simp only [List.flatMap_nil, List.append_nil, List.length_append, beBytes_length]
            at hlong
          omega
        | cons f fs =>
          rw [List.getLast?_cons_cons] at he
          exact hlast hm e he
      · simp only [List.flatMap_cons, extBytes, hel, List.append_assoc]
    · split at H
      · rename_i hm
        simp only [Option.some.injEq, Prod.mk.injEq] at H
        obtain ⟨rfl, rfl⟩ := H
        rw [macLength_iff] at hm
        refine ⟨by simp, ?_, by simp, by simp⟩
        rcases hm with h | h | h
        · exact Or.inl (List.length_eq_zero_iff.mp h)
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr h)
      · simp at H

/-- `readFields` reads back the octets of valid fields and a MAC of 0,
    20 or 24 octets, given enough fuel. -/
theorem readFields_bytes (es : List ExtField) (mac : List UInt8) (fuel : Nat)
    (hv : ∀ e ∈ es, ExtValid e) (hmac : mac = [] ∨ mac.length = 20 ∨ mac.length = 24)
    (hlast : mac = [] → ∀ e ∈ es.getLast?, 28 ≤ e.length)
    (hfuel : (es.flatMap extBytes ++ mac).length < fuel) :
    readFields fuel (es.flatMap extBytes ++ mac) = some (es, mac) := by
  induction es generalizing fuel with
  | nil =>
    obtain ⟨fuel, rfl⟩ : ∃ k, fuel = k + 1 := ⟨fuel - 1, by omega⟩
    have hm : mac.length = 0 ∨ mac.length = 20 ∨ mac.length = 24 := by
      rcases hmac with rfl | h | h <;> simp_all
    unfold readFields
    simp only [List.flatMap_nil, List.nil_append]
    rw [ite_eq_right (by rw [longer_iff]; omega), ite_eq_left ((macLength_iff _).mpr hm)]
  | cons e es ih =>
    obtain ⟨fuel, rfl⟩ : ∃ k, fuel = k + 1 := ⟨fuel - 1, by omega⟩
    have he := hv e (by simp)
    have he16 : 16 ≤ e.length := he.2.1
    have hes : ∀ x ∈ es, ExtValid x := fun x hx => hv x (by simp [hx])
    have hrest := flatMap_extBytes_length es hes
    simp only [List.flatMap_cons, List.length_append, extBytes_length] at hfuel
    have hlong : 24 < (extBytes e ++ (es.flatMap extBytes ++ mac)).length := by
      simp only [List.length_append, extBytes_length]
      cases es with
      | nil =>
        rcases hmac with rfl | h | h
        · have := hlast rfl e (by simp)
          omega
        · omega
        · omega
      | cons f fs =>
        simp only [List.length_cons] at hrest
        omega
    have hrec := ih fuel hes
      (by
        intro hm x hx
        cases es with
        | nil => simp at hx
        | cons f fs =>
          exact hlast hm x (by rw [List.getLast?_cons_cons]; exact hx))
      (by simp only [List.length_append] at hfuel ⊢; omega)
    unfold readFields
    simp only [List.flatMap_cons, List.append_assoc]
    rw [ite_eq_left ((longer_iff _ _).mpr (by simpa [List.append_assoc] using hlong))]
    simp only [extBytes, List.append_assoc, bind, readBE_append 2 _ _ (by simpa using he.1),
      Option.bind_some, readBE_append 2 _ _ (by simpa using he.2.2.2)]
    have hg : (decide (16 ≤ e.length) && e.length % 4 == 0) = true := by
      simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
      exact ⟨he.2.1, he.2.2.1⟩
    have hb : e.length - 4 = e.body.length := by simp only [ExtField.length]; omega
    simp only [hg, guard, ite_true, Option.bind_some, hb, take?_append _ _ _ rfl, hrec, pure]

/-- A field whose Length runs past the end, after valid fields, makes
    `readFields` refuse. -/
theorem readFields_overrun (es : List ExtField) (type len : Nat) (r : List UInt8) (fuel : Nat)
    (hv : ∀ e ∈ es, ExtValid e) (hlen : len < 2 ^ 16) (hr : 24 < 4 + r.length)
    (hover : 4 + r.length < len) :
    readFields fuel (es.flatMap extBytes ++ (beBytes 2 type ++ beBytes 2 len ++ r)) = none := by
  induction es generalizing fuel with
  | nil =>
    cases fuel with
    | zero => rfl
    | succ fuel =>
      unfold readFields
      simp only [List.flatMap_nil, List.nil_append]
      rw [ite_eq_left ((longer_iff _ _).mpr (by simp [beBytes_length]; omega))]
      simp only [bind, List.append_assoc, readBE_append_mod, Option.bind_some,
        readBE_append 2 _ _ (by simpa using hlen)]
      rw [take?_none _ _ (by omega)]
      cases (guard (decide (16 ≤ len) && len % 4 == 0) : Option Unit) <;> rfl
  | cons e es ih =>
    cases fuel with
    | zero => rfl
    | succ fuel =>
      have he := hv e (by simp)
      have hes : ∀ x ∈ es, ExtValid x := fun x hx => hv x (by simp [hx])
      unfold readFields
      simp only [List.flatMap_cons, List.append_assoc]
      rw [ite_eq_left ((longer_iff _ _).mpr (by
        simp only [List.length_append, beBytes_length, extBytes_length]; omega))]
      simp only [extBytes, List.append_assoc, bind, readBE_append 2 _ _ (by simpa using he.1),
        Option.bind_some, readBE_append 2 _ _ (by simpa using he.2.2.2)]
      have hg : (decide (16 ≤ e.length) && e.length % 4 == 0) = true := by
        simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
        exact ⟨he.2.1, he.2.2.1⟩
      have hb : e.length - 4 = e.body.length := by simp only [ExtField.length]; omega
      have := ih fuel hes
      simp only [List.append_assoc] at this
      simp only [hg, guard, ite_true, Option.bind_some, hb, take?_append _ _ _ rfl, this]
      rfl

/-- What `readTail` gives back. -/
theorem readTail_some (v : Nat) (t : List UInt8) (es : List ExtField) (mac : List UInt8)
    (H : readTail v t = some (es, mac)) :
    (∀ e ∈ es, ExtValid e) ∧ (v ≠ 4 → es = []) ∧ MacValid es mac ∧
      (mac = [] → ∀ e ∈ es.getLast?, 28 ≤ e.length) ∧ t = es.flatMap extBytes ++ mac := by
  unfold readTail at H
  split at H
  · rename_i h0
    simp only [Option.some.injEq, Prod.mk.injEq] at H
    obtain ⟨rfl, rfl⟩ := H
    subst h0
    exact ⟨by simp, fun _ => rfl, Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩)), by simp, by simp⟩
  · split at H
    · rename_i hv4
      obtain ⟨hv, hmac, hlast, rfl⟩ := readFields_some _ _ _ _ H
      have hm : MacValid es mac := by
        unfold MacValid
        rcases hmac with h | h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr (Or.inl h))
      exact ⟨hv, fun h => absurd hv4 h, hm, hlast, rfl⟩
    · split at H
      · rename_i hm
        simp only [Option.some.injEq, Prod.mk.injEq] at H
        obtain ⟨rfl, rfl⟩ := H
        rw [macLength_iff] at hm
        refine ⟨by simp, fun _ => rfl, ?_, by simp, by simp⟩
        unfold MacValid
        rcases hm with h | h | h
        · exact Or.inl (List.length_eq_zero_iff.mp h)
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr (Or.inl h))
      · simp at H

/-- `readTail` reads back the octets of fields and a MAC that the rules
    allow. -/
theorem readTail_bytes (v : Nat) (es : List ExtField) (mac : List UInt8)
    (hver : v = 3 ∨ v = 4) (h3 : v = 3 → es = []) (hv : ∀ e ∈ es, ExtValid e)
    (hmac : MacValid es mac) (hlast : mac = [] → ∀ e ∈ es.getLast?, 28 ≤ e.length) :
    readTail v (es.flatMap extBytes ++ mac) = some (es, mac) := by
  unfold readTail
  split
  · rename_i h0
    -- Four octets hold no field, so they are the MAC.
    cases es with
    | nil =>
      simp only [List.flatMap_nil, List.nil_append] at h0 ⊢
    | cons e es =>
      have he := (hv e (by simp)).2.1
      have := congrArg List.length h0
      simp only [List.flatMap_cons, List.length_append, extBytes_length] at this
      simp at this
      omega
  · rename_i h0
    have hmac' : mac = [] ∨ mac.length = 20 ∨ mac.length = 24 := by
      rcases hmac with h | h | h | ⟨rfl, rfl⟩
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)
      · simp at h0
    split
    · exact readFields_bytes es mac _ hv hmac' hlast (by omega)
    · rename_i hv4
      have hes : es = [] := h3 (by omega)
      subst hes
      simp only [List.flatMap_nil, List.nil_append]
      rw [ite_eq_left ((macLength_iff _).mpr (by rcases hmac' with rfl | h | h <;> simp_all))]

end NtpProofs
