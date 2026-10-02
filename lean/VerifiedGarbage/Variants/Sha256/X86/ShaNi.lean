import VerifiedGarbage.Proof.Sha256.X86.Variants.Interface
import VerifiedGarbage.Proof.Sha256.X86.ShaNi.Verified

/-!
# SHA-256 on x86 with the SHA extensions

A variant of `Sha256` on x86 (see `TCB/Emit.lean`): `vg_sha256_compress_shani`,
which needs the SHA extensions and SSSE3, and the streaming `update` and
`finalize` made with it, which HMAC's and PBKDF2's functions call
(`Generic/Sha256/X86/`).
-/
namespace VG.Variants.Sha256.X86.ShaNi
open VG VG.X86
open VG.Proof.Hmac.Generic.X86 (Sha256Stream sha256H nosp_of)
open VG.Proof.Sha256.X86.Stream (params dims)
open VG.Proof.Sha256 (md)
open VG.Proof.MdStream VG.Proof.MdStream.X86

abbrev cmpN := "vg_sha256_compress_shani"
abbrev cmpC := Impl.Sha256.X86.ShaNi.compress

abbrev sha256Update := Impl.MdStream.X86.update params cmpN cmpC
materialize_code sha256Update
abbrev sha256Finalize := Impl.MdStream.X86.finalize params cmpN cmpC
materialize_code sha256Finalize
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

/-- The streaming functions made with the SHA-NI compression function. -/
def stream : Sha256Stream where
  suffix := "_shani"
  upd := sha256Update
  fin := sha256Finalize
  updOK := Proof.Sha256.X86.Stream.update_of callee update_ct
  finOK := Proof.Sha256.X86.Stream.finalize_of callee finalize_ct
  updSp := nosp_of (by lit_decide)
  finSp := nosp_of (by lit_decide)
  updSU := by lit_decide
  finSU := by lit_decide

materialize_code sha256HInit := (sha256H stream).init
materialize_code sha256HFinalize := (sha256H stream).finalize
materialize_code sha256HIterate := Impl.Pbkdf2.Generic.X86.iterate (sha256H stream)

def variant : Proof.Sha256.X86.Variants.Backend where
  stream := stream
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

end VG.Variants.Sha256.X86.ShaNi
