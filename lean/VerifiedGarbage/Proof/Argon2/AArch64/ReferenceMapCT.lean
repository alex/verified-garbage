import VerifiedGarbage.Proof.Argon2.AArch64.ReferenceMapLaneCT
import VerifiedGarbage.Proof.Argon2.AArch64.Relative
import VerifiedGarbage.Proof.Argon2.AArch64.Wrap

/-! Complete reference mapping has no secret-dependent execution trace. -/

namespace VG.Proof.Argon2.AArch64.ReferenceMap

open VG VG.AArch64 VG.Impl.Argon2.AArch64.ReferenceMap

theorem relativeArgs_secret_rel :
    RelCT isa (fun s t => s.sp = t.sp) (.block relativeArgs) (fun s t => s.sp = t.sp) :=
  (RelCT.taintRegs (τ := Taint.ofRegs [])
    (fun _ _ h => ⟨h, by simp [Taint.mem_ofRegs]⟩) [] (by taint_decide)).mono
    (fun _ _ h => h) (fun _ _ h => h.1)

theorem wrapArgs_secret_rel :
    RelCT isa (fun s t => s.sp = t.sp) (.block wrapArgs) (fun s t => s.sp = t.sp) :=
  (RelCT.taintRegs (τ := Taint.ofRegs [])
    (fun _ _ h => ⟨h, by simp [Taint.mem_ofRegs]⟩) [] (by taint_decide)).mono
    (fun _ _ h => h) (fun _ _ h => h.1)

theorem tail_secret_rel :
    RelCT isa (fun s t => s.sp = t.sp) (.seq relative finish) (fun s t => s.sp = t.sp) :=
  (relativeArgs_secret_rel.seq Relative.code_secret_rel).seq
    (wrapArgs_secret_rel.seq Wrap.code_secret_rel)

theorem code_rel (p : Spec.Argon2.Params) (pass lane slice index : Nat) :
    RelCT isa (Related p pass lane slice index) code (fun s t => s.sp = t.sp) :=
  (prepareLanes_rel p pass lane slice index).seq (window_rel.seq tail_secret_rel)

end VG.Proof.Argon2.AArch64.ReferenceMap
