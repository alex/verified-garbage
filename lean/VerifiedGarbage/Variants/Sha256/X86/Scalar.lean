import VerifiedGarbage.Proof.Sha256.X86.Variants.Interface
import VerifiedGarbage.Proof.Framework.X86.Lit

/-! Scalar SHA-256 is one backend; its generic callers are emitted with it. -/
namespace VG.Variants.Sha256.X86.Scalar

open VG.X86

materialize_code sha256HInit := Impl.Hmac.Sha256.X86.init "vg_sha256_compress" Impl.Sha256.X86.compress
materialize_code sha256HFinalize := Impl.Hmac.Sha256.X86.finalize "vg_sha256_compress" Impl.Sha256.X86.compress
materialize_code sha256HIterate := Impl.Pbkdf2.Sha256.X86.iterate "vg_sha256_compress" Impl.Sha256.X86.compress
materialize_code sha256HInitAny :=
  (Proof.Hmac.Generic.X86.sha256H "vg_sha256_compress" Impl.Sha256.X86.compress "").initAny
materialize_code sha256HFin :=
  (Proof.Hmac.Generic.X86.sha256H "vg_sha256_compress" Impl.Sha256.X86.compress "").finalize

/-- Generic registration preserves every scalar construction instruction. -/
theorem scalar_code_unchanged :
    Impl.Hmac.Sha256.X86.init "vg_sha256_compress" Impl.Sha256.X86.compress = Impl.Hmac.X86.init ∧
    Impl.Hmac.Sha256.X86.finalize "vg_sha256_compress" Impl.Sha256.X86.compress = Impl.Hmac.X86.finalize ∧
    Impl.Pbkdf2.Sha256.X86.iterate "vg_sha256_compress" Impl.Sha256.X86.compress = Impl.Pbkdf2.X86.iterate :=
  ⟨rfl, rfl, rfl⟩

def variant : Proof.Sha256.X86.Variants.Backend where
  cmpN := "vg_sha256_compress"
  cmpC := Impl.Sha256.X86.compress
  cmp := Proof.Sha256.X86.compress_verified
  cmpSp := NoSp.of_all (by lit_decide)
  cmpStack := by lit_decide
  initCt := Proof.Hmac.X86.Init.init_ct
  finCt := Proof.Hmac.X86.Finalize.finalize_ct
  finHashSp := Proof.Hmac.X86.Finalize.finalizeHash_nosp
  finHashStack := Proof.Hmac.X86.Finalize.finalizeHash_stack
  iterCt := Proof.Pbkdf2.X86.iterate_ct
  suffix := ""
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
  hmac :=
    { callee := Proof.Sha256.X86.Stream.callee
      updCt := Proof.Sha256.X86.Stream.Update.update_ct
      finCt := Proof.Sha256.X86.Stream.Finalize.finalize_ct
      updSp := by rw [← Proof.Sha256.X86.Stream.update_eq]; exact NoSp.of_all (by lit_decide)
      finSp := by rw [← Proof.Sha256.X86.Stream.finalize_eq]; exact NoSp.of_all (by lit_decide)
      updSU := by rw [← Proof.Sha256.X86.Stream.update_eq]; lit_decide
      finSU := by rw [← Proof.Sha256.X86.Stream.finalize_eq]; lit_decide }
  hmacInitSp := Code.all_of_allInstrs (by lit_decide)
  hmacFinSp := Code.all_of_allInstrs (by lit_decide)

end VG.Variants.Sha256.X86.Scalar
