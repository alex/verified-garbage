import VerifiedGarbage.Proof.Ed25519.X86_64.ScalarMain
import VerifiedGarbage.Proof.Ed25519.X86_64.PublicKey.Base

/-! The zero-extended scalar is exactly the corrected specification's challenge. -/
namespace VG.Proof.Ed25519.X86_64.VerifyMessage
open VG
open VG.Spec.Ed25519

theorem reduced_challenge (digest : List Byte) :
    encodeLE 64 (decodeLE digest % L) = scalarReduce digest ++ encodeLE 32 0 := by
  simp only [scalarReduce, Proof.Ed25519.X86_64.encodeLE_eq]
  rw [show (64 : Nat) = 32 + 32 from rfl, Proof.X25519.leBytes_add]
  have hL : L ≤ 256 ^ 32 := by decide
  have hpos : 0 < L := by decide
  rw [Nat.div_eq_of_lt (Nat.lt_of_lt_of_le (Nat.mod_lt _ hpos) hL)]

theorem zero_words (m : Mem) (p : Addr)
    (h0 : m.readW p 64 = 0) (h1 : m.readW (p + 8) 64 = 0)
    (h2 : m.readW (p + 16) 64 = 0)
    (h3 : m.readW (p + 24) 64 = 0) :
    bytesAt m p 32 = encodeLE 32 0 := by
  rw [Proof.Ed25519.X86_64.encodeLE_eq]
  exact Proof.X25519.bytesAt_leBytes_words64 m p 0
    (by rw [h0]; rfl) (by rw [h1]; rfl) (by rw [h2]; rfl) (by rw [h3]; rfl)

end VG.Proof.Ed25519.X86_64.VerifyMessage
