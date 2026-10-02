import VerifiedGarbage.Proof.Sha256.X86.Variants.Interface
import VerifiedGarbage.Proof.Framework.X86.Lit

/-! Scalar SHA-256 is one backend; its generic callers are emitted with it. -/
namespace VG.Variants.Sha256.X86.Scalar

open VG.X86

materialize_code sha256HInit := Impl.Hmac.Sha256.X86.init "vg_sha256_compress" Impl.Sha256.X86.compress
materialize_code sha256HFinalize := Impl.Hmac.Sha256.X86.finalize "vg_sha256_compress" Impl.Sha256.X86.compress
materialize_code sha256HIterate := Impl.Pbkdf2.Sha256.X86.iterate "vg_sha256_compress" Impl.Sha256.X86.compress
materialize_code sha256HPbkdf2 := (Proof.Pbkdf2.Whole.X86.sha256Fns "" "vg_sha256_compress" Impl.Sha256.X86.compress
  Impl.Sha256.X86.Stream.update Impl.Sha256.X86.Stream.finalize).pbkdf2

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
  updC := Impl.Sha256.X86.Stream.update
  upd := Proof.Sha256.X86.Stream.Update.update_verified
  updNoSp := NoSp.of_all (by lit_decide)
  updStack := by lit_decide
  finC := Impl.Sha256.X86.Stream.finalize
  fin := Proof.Sha256.X86.Stream.Finalize.finalize_verified
  finNoSp := NoSp.of_all (by lit_decide)
  finStack := by lit_decide
  initNoSp := NoSp.of_all (by lit_decide)
  initStack := by lit_decide
  finalizeNoSp := NoSp.of_all (by lit_decide)
  finalizeStack := by lit_decide
  iterNoSp := NoSp.of_all (by lit_decide)
  iterStack := by lit_decide
  pbkdf2Sp := Code.all_of_allInstrs (by lit_decide)

end VG.Variants.Sha256.X86.Scalar
