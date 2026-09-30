import VerifiedGarbage.Proof.Ed25519.Bytes

/-! Untrusted: split the fixed-width signature at the R/S boundary. -/

namespace VG.Proof.Ed25519

open VG VG.Spec.Ed25519

theorem signatureBytes_split (m : Mem) (p : Addr) :
    bytesAt m p 64 = bytesAt m p 32 ++ bytesAt m (p + BitVec.ofNat 64 32) 32 :=
  Proof.X25519.bytesAt_add m p 32 32

theorem signatureBytes_take (m : Mem) (p : Addr) : (bytesAt m p 64).take 32 = bytesAt m p 32 := by
  have h : (bytesAt m p 32).length = 32 := Proof.X25519.length_bytesAt m p 32
  rw [signatureBytes_split]
  simpa only [h] using List.take_left (l₁ := bytesAt m p 32) (l₂ := bytesAt m (p + BitVec.ofNat 64 32) 32)

theorem signatureBytes_drop (m : Mem) (p : Addr) :
    (bytesAt m p 64).drop 32 = bytesAt m (p + BitVec.ofNat 64 32) 32 := by
  have h : (bytesAt m p 32).length = 32 := Proof.X25519.length_bytesAt m p 32
  rw [signatureBytes_split]
  simpa only [h] using List.drop_left (l₁ := bytesAt m p 32) (l₂ := bytesAt m (p + BitVec.ofNat 64 32) 32)

end VG.Proof.Ed25519
