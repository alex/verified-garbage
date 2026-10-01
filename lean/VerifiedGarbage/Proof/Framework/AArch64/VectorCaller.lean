import VerifiedGarbage.Proof.Framework.AArch64.VectorTaint
import VerifiedGarbage.Proof.Framework.RelCT

/-! Caller-facing adapters for vector-aware constant-time analysis.
Initial vectors are secret, so callers only need their existing public-GPR facts.
-/
namespace VG.AArch64.VectorTaint

theorem agree_initial {τ : AArch64.Taint.T} {x y : State}
    (h : AArch64.Taint.Agree τ x y) : Agree (τ, RegSet.empty) x y :=
  ⟨h, fun r hr => False.elim (RegSet.not_mem_empty r hr)⟩

theorem constantTime {Pre : State → Prop} {Pub : State → State → Prop} {c : Prog isa}
    (τ : AArch64.Taint.T)
    (hp : ∀ x y, Pre x → Pre y → Pub x y → AArch64.Taint.Agree τ x y)
    {hc : VG.Taint.Hint T}
    (h : (taint.check (τ, RegSet.empty) c hc).isSome = true) : ConstantTime isa Pre Pub c :=
  VG.Taint.constantTime (A := taint) (τ, RegSet.empty)
    (fun x y hx hy hxy => agree_initial (hp x y hx hy hxy)) h

theorem relCT {P : State → State → Prop} {c : Prog isa} (τ : AArch64.Taint.T)
    (hp : ∀ x y, P x y → AArch64.Taint.Agree τ x y) {hc : VG.Taint.Hint T}
    (h : (taint.check (τ, RegSet.empty) c hc).isSome = true) : RelCT isa P c fun _ _ => True :=
  VG.RelCT.taint (A := taint) (τ, RegSet.empty)
    (fun x y hxy => agree_initial (hp x y hxy)) h

theorem relRegs {P : State → State → Prop} {c : Prog isa} (rs : List Reg)
    (hp : ∀ x y, P x y → x.sp = y.sp ∧ ∀ r ∈ rs, x.gpr r = y.gpr r)
    {hc : VG.Taint.Hint T}
    (h : (taint.check (ofRegs rs) c hc).isSome = true) : RelCT isa P c fun _ _ => True :=
  relCT (AArch64.Taint.ofRegs rs)
    (fun x y hxy => ⟨(hp x y hxy).1, fun r hr =>
      (hp x y hxy).2 r (AArch64.Taint.mem_ofRegs.mp hr)⟩) h

end VG.AArch64.VectorTaint
