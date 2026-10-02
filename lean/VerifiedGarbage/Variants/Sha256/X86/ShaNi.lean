import VerifiedGarbage.Proof.Sha256.X86.Variants.Interface
import VerifiedGarbage.Proof.Sha256.X86.ShaNi.Verified

/-! SHA-NI compression and all generic SHA-256 constructions on x86 (PBKDF2's whole
derivation among them). -/
namespace VG.Variants.Sha256.X86.ShaNi
open VG VG.X86
open VG.Proof.Sha256.X86.Stream (params dims)
open VG.Proof.Sha256 (md)
open VG.Proof.MdStream VG.Proof.MdStream.X86

abbrev cmpN := "vg_sha256_compress_shani"
abbrev cmpC := Impl.Sha256.X86.ShaNi.compress

abbrev sha256Update := Impl.MdStream.X86.update params cmpN cmpC
materialize_code sha256Update
abbrev sha256Finalize := Impl.MdStream.X86.finalize params cmpN cmpC
materialize_code sha256Finalize
abbrev sha256HInit := Impl.Hmac.Sha256.X86.init cmpN cmpC
materialize_code sha256HInit
abbrev sha256HFinalize := Impl.Hmac.Sha256.X86.finalize cmpN cmpC
materialize_code sha256HFinalize
abbrev sha256HFinalizeHash := Impl.Hmac.Sha256.X86.finalizeHash cmpN cmpC
materialize_code sha256HFinalizeHash
abbrev sha256HIterate := Impl.Pbkdf2.Sha256.X86.iterate cmpN cmpC
materialize_code sha256HIterate
abbrev sha256HPbkdf2 :=
  (Proof.Pbkdf2.Whole.X86.sha256Fns "_shani" cmpN cmpC sha256Update sha256Finalize).pbkdf2
materialize_code sha256HPbkdf2

theorem callee : CalleeOk (P := params) md cmpC :=
  ⟨Proof.Sha256.X86.ShaNi.compress_verified.1, Proof.Sha256.X86.ShaNi.compress_nosp,
    Proof.Sha256.X86.ShaNi.compress_stack⟩

theorem update_ct : ConstantTime isa (updK (P := params) md 160).pre
    (updK (P := params) md 160).pub sha256Update :=
  VG.Taint.constantTime (A := sseTaint) (Proof.MdStream.X86.Update.τ₀ params 160)
    (fun _ _ h₁ h₂ hp => Proof.MdStream.X86.Update.agree₀ dims h₁ h₂ hp) (by taint_decide)

theorem finalize_ct : ConstantTime isa (finK (P := params) md 160).pre
    (finK (P := params) md 160).pub sha256Finalize :=
  VG.Taint.constantTime (A := sseTaint) (Proof.MdStream.X86.Finalize.τ₀ params 160)
    (fun _ _ h₁ h₂ hp => Proof.MdStream.X86.Finalize.agree₀ dims h₁ h₂ hp) (by taint_decide)

theorem init_ct : ConstantTime isa Proof.Hmac.initSha256X86.pre Proof.Hmac.initSha256X86.pub sha256HInit :=
  VG.Taint.constantTime (A := sseTaint) Proof.Hmac.X86.Init.τ₀
    (fun _ _ h₁ h₂ hp => Proof.Hmac.X86.Init.agree₀ h₁ h₂ hp) (by taint_decide)

theorem hfinalize_ct : ConstantTime isa Proof.Hmac.finalizeSha256X86.pre
    Proof.Hmac.finalizeSha256X86.pub sha256HFinalize :=
  VG.Taint.constantTime (A := sseTaint) Proof.Hmac.X86.Finalize.τ₀
    (fun _ _ h₁ h₂ hp => Proof.Hmac.X86.Finalize.agree₀ h₁ h₂ hp)
    (by taint_decide_weaken Proof.Hmac.X86.Finalize.forget)

theorem iterate_ct : ConstantTime isa Proof.Pbkdf2.iterateSha256X86.pre
    Proof.Pbkdf2.iterateSha256X86.pub sha256HIterate :=
  VG.Taint.constantTime (A := sseTaint) Proof.Pbkdf2.X86.τ₀
    (fun _ _ h₁ h₂ hp => Proof.Pbkdf2.X86.agree₀ h₁ h₂ hp) (by taint_decide)

theorem compress_shared : Verified X86.target cmpC (Spec.Sha256.compressContract X86.abi) :=
  (Proof.Sha256.X86.Shared.compressWide_of Proof.Sha256.X86.ShaNi.compress_verified
    Proof.Sha256.X86.Shared.compressWide_implies.sat_left).of_implies
      Proof.Sha256.X86.Shared.compressWide_implies

theorem update_shared : Verified X86.target sha256Update (Spec.Sha256.updateContract X86.abi 20) :=
  (Proof.Sha256.X86.Shared.updateWide_of (Proof.Sha256.X86.Stream.update_of callee update_ct)
    Proof.Sha256.X86.Shared.updateWide_implies.sat_left).of_implies
      Proof.Sha256.X86.Shared.updateWide_implies

theorem finalize_shared : Verified X86.target sha256Finalize (Spec.Sha256.finalizeContract X86.abi 20) :=
  (Proof.Sha256.X86.Shared.finalizeWide_of (Proof.Sha256.X86.Stream.finalize_of callee finalize_ct)
    Proof.Sha256.X86.Shared.finalizeWide_implies.sat_left).of_implies
      Proof.Sha256.X86.Shared.finalizeWide_implies

def variant : Proof.Sha256.X86.Variants.Backend where
  cmpN := cmpN
  cmpC := cmpC
  cmp := Proof.Sha256.X86.ShaNi.compress_verified
  cmpSp := Proof.Sha256.X86.ShaNi.compress_nosp
  cmpStack := Proof.Sha256.X86.ShaNi.compress_stack
  initCt := init_ct
  finCt := hfinalize_ct
  finHashSp := NoSp.of_all (by lit_decide)
  finHashStack := by lit_decide
  iterCt := iterate_ct
  suffix := "_shani"
  features := ["sha", "ssse3"]
  functions := [
    { api := Spec.Sha256.compressApi
      code := cmpC
      contract := Spec.Sha256.compressContract X86.abi
      verified := compress_shared
      ofSig := ⟨_, _, _, rfl⟩
      ofApi := rfl
      spSafe := Code.all_of_allInstrs (by lit_decide) },
    { api := Spec.Sha256.updateApi
      code := sha256Update
      contract := Spec.Sha256.updateContract X86.abi 20
      stack := 20
      verified := update_shared
      ofSig := ⟨_, _, _, rfl⟩
      ofApi := rfl
      spSafe := Code.all_of_allInstrs (by lit_decide) },
    { api := Spec.Sha256.finalizeApi
      code := sha256Finalize
      contract := Spec.Sha256.finalizeContract X86.abi 20
      stack := 20
      verified := finalize_shared
      ofSig := ⟨_, _, _, rfl⟩
      ofApi := rfl
      spSafe := Code.all_of_allInstrs (by lit_decide) }]
  initSp := Code.all_of_allInstrs (by lit_decide)
  finSp := Code.all_of_allInstrs (by lit_decide)
  iterSp := Code.all_of_allInstrs (by lit_decide)
  updC := sha256Update
  upd := Proof.Sha256.X86.Stream.update_of callee update_ct
  updNoSp := NoSp.of_all (by lit_decide)
  updStack := by lit_decide
  finC := sha256Finalize
  fin := Proof.Sha256.X86.Stream.finalize_of callee finalize_ct
  finNoSp := NoSp.of_all (by lit_decide)
  finStack := by lit_decide
  initNoSp := NoSp.of_all (by lit_decide)
  initStack := by lit_decide
  finalizeNoSp := NoSp.of_all (by lit_decide)
  finalizeStack := by lit_decide
  iterNoSp := NoSp.of_all (by lit_decide)
  iterStack := by lit_decide
  pbkdf2Sp := Code.all_of_allInstrs (by lit_decide)

end VG.Variants.Sha256.X86.ShaNi
