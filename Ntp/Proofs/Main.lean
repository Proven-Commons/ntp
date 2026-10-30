/-
  The statements of `Ntp/Spec.lean`, each proved from the lemmas in the
  other files of `Ntp/Proofs/`. `lake comparator` checks that each theorem
  here is exactly the one in `Ntp/Spec.lean`.
-/

import Ntp.Proofs.Packet
import Ntp.Proofs.Time
import Ntp.Spec.Examples

namespace Ntp.Spec

theorem decode_iff (b : List UInt8) (p : Packet) :
    Ntp.decode b = some p ↔ Valid p ∧ b = packetBytes p :=
  NtpProofs.decode_iff b p

theorem encode_eq (p : Packet) (hp : Valid p) : Ntp.encode p = packetBytes p :=
  NtpProofs.encode_eq p hp

theorem decode_encode (p : Packet) : Ntp.decode (Ntp.encode p) = some p ↔ Valid p := by
  constructor
  · intro h
    exact ((decode_iff _ _).mp h).1
  · intro hp
    rw [encode_eq p hp]
    exact (decode_iff _ _).mpr ⟨hp, rfl⟩

theorem encode_decode (b : List UInt8) (p : Packet) (h : Ntp.decode b = some p) :
    Ntp.encode p = b := by
  obtain ⟨hp, rfl⟩ := (decode_iff _ _).mp h
  exact encode_eq p hp

theorem decode_short (b : List UInt8) (h : b.length < 48) : Ntp.decode b = none := by
  cases hd : Ntp.decode b with
  | none => rfl
  | some p =>
    obtain ⟨-, rfl⟩ := (decode_iff _ _).mp hd
    simp only [packetBytes, List.length_append, NtpProofs.headerBytes_length] at h
    omega

/-- The first octet of an accepted packet is LI, VN and Mode. -/
theorem first_octet (x : UInt8) (b : List UInt8) (p : Packet) (hd : Ntp.decode (x :: b) = some p) :
    x.toNat = p.header.leap * 64 + p.header.version * 8 + p.header.mode ∧
      HeaderValid p.header := by
  obtain ⟨⟨hv, -⟩, he⟩ := (decode_iff _ _).mp hd
  have hv' := hv
  obtain ⟨hl, hver, hm1, hm2, -⟩ := hv'
  unfold packetBytes headerBytes at he
  simp only [List.append_assoc, List.cons_append, List.cons.injEq] at he
  have := congrArg UInt8.toNat he.1
  rw [NtpProofs.toNat_toUInt8 _ (by omega)] at this
  exact ⟨this, hv⟩

theorem decode_version (x : UInt8) (b : List UInt8)
    (h : x.toNat / 8 % 8 ≠ 3 ∧ x.toNat / 8 % 8 ≠ 4) : Ntp.decode (x :: b) = none := by
  cases hd : Ntp.decode (x :: b) with
  | none => rfl
  | some p =>
    obtain ⟨hx, hl, hver, hm1, hm2, -⟩ := first_octet x b p hd
    omega

theorem decode_mode (x : UInt8) (b : List UInt8)
    (h : x.toNat % 8 = 0 ∨ x.toNat % 8 = 6 ∨ x.toNat % 8 = 7) : Ntp.decode (x :: b) = none := by
  cases hd : Ntp.decode (x :: b) with
  | none => rfl
  | some p =>
    obtain ⟨hx, hl, hver, hm1, hm2, -⟩ := first_octet x b p hd
    omega

theorem decode_ext_overrun (h : List UInt8) (es : List ExtField) (type len : Nat)
    (r : List UInt8) (hh : h.length = 48) (hes : ∀ e ∈ es, ExtValid e) (hlen : len < 2 ^ 16)
    (hr : 24 < 4 + r.length) (hover : 4 + r.length < len) :
    Ntp.decode (h ++ es.flatMap extBytes ++ beBytes 2 type ++ beBytes 2 len ++ r) = none := by
  unfold Ntp.decode
  cases hh' : Ntp.readHeader (h ++ es.flatMap extBytes ++ beBytes 2 type ++ beBytes 2 len ++ r)
    with
  | none => rfl
  | some ht =>
    obtain ⟨hd, t⟩ := ht
    obtain ⟨-, he⟩ := NtpProofs.readHeader_some _ _ _ hh'
    have ht : t = es.flatMap extBytes ++ (beBytes 2 type ++ beBytes 2 len ++ r) := by
      simp only [List.append_assoc] at he ⊢
      exact (List.append_inj he (by rw [hh, NtpProofs.headerBytes_length])).2.symm
    subst ht
    simp only [bind, Option.bind_some]
    have hlong : 24 < (es.flatMap extBytes ++ (beBytes 2 type ++ beBytes 2 len ++ r)).length := by
      simp only [List.length_append, NtpProofs.beBytes_length]
      omega
    unfold Ntp.readTail
    rw [ite_eq_right (fun h0 => by rw [h0] at hlong; simp at hlong)]
    split
    · rw [NtpProofs.readFields_overrun es type len r _ hes hlen hr hover]
      rfl
    · rw [ite_eq_right (fun hm => by rw [NtpProofs.macLength_iff] at hm; omega)]
      rfl

theorem toUnix_zero (era : Int) : Ntp.toUnix era 0 = none :=
  NtpProofs.toUnix_zero era

theorem toUnix_spec (era : Int) (raw : Nat) (s : Int) (f : Nat) :
    Ntp.toUnix era raw = some (s, f) ↔
      raw ≠ 0 ∧ raw < 2 ^ 64 ∧ f < 2 ^ 32 ∧
        s * 2 ^ 32 + f = era * 2 ^ 64 + raw - unixEpoch * 2 ^ 32 :=
  NtpProofs.toUnix_spec era raw s f

theorem fromUnix_toUnix (era : Int) (raw : Nat) (s : Int) (f : Nat)
    (h : Ntp.toUnix era raw = some (s, f)) : Ntp.fromUnix s f = some (era, raw) :=
  NtpProofs.fromUnix_toUnix era raw s f h

theorem toUnix_fromUnix (s : Int) (f : Nat) (era : Int) (raw : Nat)
    (h : Ntp.fromUnix s f = some (era, raw)) : Ntp.toUnix era raw = some (s, f) :=
  NtpProofs.toUnix_fromUnix s f era raw h

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
  decide +kernel

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
  decide +kernel

end Ntp.Spec
