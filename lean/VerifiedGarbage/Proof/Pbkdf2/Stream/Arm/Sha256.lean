import VerifiedGarbage.Proof.Pbkdf2.Stream.Arm.Hashes
import VerifiedGarbage.Proof.Sha256.Arm.Shared

/-!
# SHA-256's streaming functions on 32-bit ARM

`HashOK` for SHA-256 (`sha256OK`): its streaming functions
(`vg_sha256_init`, `vg_sha256_update` and `vg_sha256_finalize`, whose
contracts for `update` and `finalize` hold from any initial hash value).
-/

namespace VG.Proof.Pbkdf2.Stream.Arm

open VG.Arm
open VG.Impl.Pbkdf2.Stream.Arm (Hash)

/-- SHA-256's functions: a 96-byte streaming state, 20 words of working
space and a 32-byte digest. -/
def sha256H : Hash := ⟨64, 96, 32, 32, 20, "vg_sha256_init", Impl.Sha256.Arm.Stream.init,
  "vg_sha256_update", Impl.Sha256.Arm.Stream.update, "vg_sha256_finalize", Impl.Sha256.Arm.Stream.finalize⟩

def sha256OK : HashOK sha256H where
  SH := Spec.Hmac.sha256S
  Wb := 160
  hS := rfl
  hD := rfl
  hB := rfl
  hDF := by decide
  hF := by decide
  hD0 := by decide
  hS0 := by decide
  hSB := by decide
  hB0 := by decide
  hBB := by decide
  hWb := by decide
  hW := by decide
  repr := Hmac.Generic.Common.sha256_repr
  init := Proof.Sha256.Arm.Stream.init_verified
  upd := Proof.Sha256.Arm.Stream.Update.update_verified.of_implies
    { pre := fun _ h => h
      post := fun _ _ _ h m hr hc => h Spec.Sha256.H0 m hr hc
      pub := fun _ _ _ _ h => h
      sat := Proof.Sha256.Arm.Stream.Update.update_verified.2.2 }
  fin := Proof.Sha256.Arm.Stream.Finalize.finalize_verified.of_implies
    { pre := fun _ h => h
      post := fun s s' _ h m hr _ hc => by
        show List.take 32 (Spec.Sha256.bytesAt s'.mem _ 32) = _
        rw [List.take_of_length_le (by simp [Spec.Sha256.bytesAt])]
        exact h Spec.Sha256.H0 m hr hc
      pub := fun _ _ _ _ h => h
      sat := Proof.Sha256.Arm.Stream.Finalize.finalize_verified.2.2 }
  initNF := by decide +kernel
  updNF := by decide +kernel
  finNF := by decide +kernel

end VG.Proof.Pbkdf2.Stream.Arm
