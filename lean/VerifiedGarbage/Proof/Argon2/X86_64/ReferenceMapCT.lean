import VerifiedGarbage.Proof.Argon2.X86_64.ReferenceMapLaneCT
import VerifiedGarbage.Proof.Argon2.X86_64.Relative
import VerifiedGarbage.Proof.Argon2.X86_64.Wrap

/-! Complete reference mapping has no secret-dependent execution trace. -/

namespace VG.Proof.Argon2.X86_64.ReferenceMap

open VG VG.X86_64 VG.Impl.Argon2.X86_64.ReferenceMap

theorem relativeArgs_secret_rel :
    RelCT isa (fun _ _ => True) (.block relativeArgs) (fun _ _ => True) :=
  RelCT.taint (A := taint) (Taint.ofRegs [])
    (fun _ _ _ => Taint.agree_ofRegs (by simp)) (by taint_decide)

theorem wrapArgs_secret_rel :
    RelCT isa (fun _ _ => True) (.block wrapArgs) (fun _ _ => True) :=
  RelCT.taint (A := taint) (Taint.ofRegs [])
    (fun _ _ _ => Taint.agree_ofRegs (by simp)) (by taint_decide)

theorem tail_secret_rel :
    RelCT isa (fun _ _ => True) (.seq relative finish) (fun _ _ => True) :=
  (relativeArgs_secret_rel.seq Relative.code_secret_rel).seq
    (wrapArgs_secret_rel.seq Wrap.code_secret_rel)

theorem code_rel (p : Spec.Argon2.Params) (pass lane slice index : Nat) :
    RelCT isa (Related p pass lane slice index) code (fun _ _ => True) :=
  (prepareLanes_rel p pass lane slice index).seq (window_rel.seq tail_secret_rel)

end VG.Proof.Argon2.X86_64.ReferenceMap
