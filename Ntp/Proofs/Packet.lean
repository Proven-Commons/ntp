import Ntp.Proofs.Header
import Ntp.Proofs.Tail

/-!
  The decoder and the encoder against `Ntp.Spec.packetBytes` and
  `Ntp.Spec.Valid`.
-/

namespace NtpProofs

open Ntp.Spec Ntp

theorem decode_some (b : List UInt8) (p : Packet) (H : decode b = some p) :
    Valid p ∧ b = packetBytes p := by
  unfold decode at H
  simp only [bind, Option.bind_eq_some_iff, Prod.exists, pure, Option.some.injEq] at H
  obtain ⟨h, t, hh, es, mac, ht, rfl⟩ := H
  obtain ⟨hv, rfl⟩ := readHeader_some _ _ _ hh
  obtain ⟨hes, h3, hmac, hlast, rfl⟩ := readTail_some _ _ _ _ ht
  refine ⟨⟨hv, hes, fun h' => h3 (by dsimp only at h'; omega), hmac, hlast⟩, ?_⟩
  simp [packetBytes, List.append_assoc]

theorem decode_bytes (p : Packet) (hp : Valid p) : decode (packetBytes p) = some p := by
  obtain ⟨hv, hes, h3, hmac, hlast⟩ := hp
  unfold decode packetBytes
  rw [List.append_assoc, readHeader_bytes _ hv]
  simp only [bind, Option.bind_some]
  rw [readTail_bytes _ _ _ hv.2.1 h3 hes hmac hlast]
  rfl

theorem decode_iff (b : List UInt8) (p : Packet) :
    decode b = some p ↔ Valid p ∧ b = packetBytes p := by
  constructor
  · exact decode_some b p
  · rintro ⟨hp, rfl⟩
    exact decode_bytes p hp

theorem writeField_eq (e : ExtField) : writeField e = extBytes e := by
  simp only [writeField, extBytes, writeBE_eq, ExtField.length]

theorem ofSigned_eq (z : Int) (h1 : -128 ≤ z) (h2 : z < 128) :
    ofSigned z = (z % 256).toNat := by
  unfold ofSigned
  split <;> omega

theorem encode_eq (p : Packet) (hp : Valid p) : encode p = packetBytes p := by
  obtain ⟨⟨hl, hver, hm1, hm2, hst, hp1, hp2, hq1, hq2, -⟩, -⟩ := hp
  have hlvm : p.header.leap * 64 + p.header.version * 8 + p.header.mode < 256 := by omega
  have hs : ∀ z : Int, -128 ≤ z → z < 128 → (z % 256).toNat < 256 := fun z _ _ => by omega
  have hw : writeField = extBytes := funext writeField_eq
  unfold encode packetBytes headerBytes signedByte
  simp only [writeBE_eq, ofSigned_eq _ hp1 hp2, ofSigned_eq _ hq1 hq2, beBytes_one _ hlvm,
    beBytes_one _ hst, beBytes_one _ (hs _ hp1 hp2), beBytes_one _ (hs _ hq1 hq2), hw,
    List.append_assoc, List.cons_append, List.nil_append]

end NtpProofs
