import VerifiedGarbage.Proof.Sha256.X86.Variants.Interface
import VerifiedGarbage.Proof.Framework.X86.Lit

/-!
# SHA-256 on x86: the scalar compression function

A variant of `Sha256` on x86 (see `TCB/Emit.lean`): `vg_sha256_compress`, in
the baseline ISA, and the streaming `update` and `finalize` made with it,
which HMAC's and PBKDF2's functions call (`Generic/Sha256/X86/`).
-/
namespace VG.Variants.Sha256.X86.Scalar

open VG.X86
open VG.Proof.Hmac.Generic.X86 (Sha256Stream)
open VG.Proof.Pbkdf2.Md.X86 (sha256M)
open VG.Proof.Sha256.X86.Variants (pbkdf2Fns)

/-- The streaming functions made with the scalar compression function. -/
def stream : Sha256Stream where
  suffix := ""
  upd := Impl.Sha256.X86.Stream.update
  fin := Impl.Sha256.X86.Stream.finalize
  updOK := Proof.Sha256.X86.Stream.Update.update_verified
  finOK := Proof.Sha256.X86.Stream.Finalize.finalize_verified
  updSp := NoSp.of_all (by lit_decide)
  finSp := NoSp.of_all (by lit_decide)
  updSU := by lit_decide
  finSU := by lit_decide

materialize_code sha256HInit := (sha256M stream "vg_sha256_compress" Impl.Sha256.X86.compress).hmacInit
materialize_code sha256HFinalize := (sha256M stream "vg_sha256_compress" Impl.Sha256.X86.compress).hmacFin
materialize_code sha256HIterate := (sha256M stream "vg_sha256_compress" Impl.Sha256.X86.compress).iterate
materialize_code sha256HPbkdf2 := (pbkdf2Fns stream "vg_sha256_compress" Impl.Sha256.X86.compress).pbkdf2

def variant : Proof.Sha256.X86.Variants.Backend where
  cmpN := "vg_sha256_compress"
  cmpC := Impl.Sha256.X86.compress
  cmp := Proof.Sha256.X86.compress_verified
  cmpSp := NoSp.of_all (by lit_decide)
  cmpStack := by lit_decide
  stream := stream
  features := []
  functions := [
    { api := Spec.Sha256.compressApi
      code := Impl.Sha256.X86.compress
      contract := Spec.Sha256.compressContract X86.abi
      verified := Proof.Sha256.X86.Shared.compress
      ofSig := ⟨_, _, _, rfl⟩
      ofApi := rfl
      spSafe := Code.all_of_allInstrs (by lit_decide) },
    { api := Spec.Sha256.updateApi
      code := Impl.Sha256.X86.Stream.update
      contract := Spec.Sha256.updateContract X86.abi 20
      stack := 20
      verified := Proof.Sha256.X86.Shared.update
      ofSig := ⟨_, _, _, rfl⟩
      ofApi := rfl
      spSafe := Code.all_of_allInstrs (by lit_decide) },
    { api := Spec.Sha256.finalizeApi
      code := Impl.Sha256.X86.Stream.finalize
      contract := Spec.Sha256.finalizeContract X86.abi 20
      stack := 20
      verified := Proof.Sha256.X86.Shared.finalize
      ofSig := ⟨_, _, _, rfl⟩
      ofApi := rfl
      spSafe := Code.all_of_allInstrs (by lit_decide) }]
  initSp := Code.all_of_allInstrs (by lit_decide)
  finSp := Code.all_of_allInstrs (by lit_decide)
  iterSp := Code.all_of_allInstrs (by lit_decide)
  pbkdf2Sp := Code.all_of_allInstrs (by lit_decide)
  initNoSp := NoSp.of_all (by lit_decide)
  initStack := by lit_decide
  finalizeNoSp := NoSp.of_all (by lit_decide)
  finalizeStack := by lit_decide
  iterNoSp := NoSp.of_all (by lit_decide)
  iterStack := by lit_decide

end VG.Variants.Sha256.X86.Scalar
