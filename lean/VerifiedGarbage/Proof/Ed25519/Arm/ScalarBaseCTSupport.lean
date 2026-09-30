import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.Framework.Arm.Taint
import VerifiedGarbage.Proof.Framework.Arm.Exec

/-! Relational composition restores public metadata from checked functional proofs. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm

abbrev CT := RelCT isa

theorem ctRegs {P : State → State → Prop} {c : Prog isa} (rs : List Reg)
    (hp : ∀ x y, P x y → ∀ r ∈ rs, x.gpr r = y.gpr r)
    {hint : VG.Taint.Hint VG.Arm.Taint.T}
    (hc : (VG.Arm.taint.check (VG.Arm.Taint.ofRegs rs) c hint).isSome = true) :
    CT P c (fun _ _ => True) :=
  RelCT.taint (A := VG.Arm.taint) (VG.Arm.Taint.ofRegs rs)
    (fun x y h => VG.Arm.Taint.agree_ofRegs (hp x y h)) hc

theorem ctRegsKeeping {P : State → State → Prop} {c : Prog isa} (rs out : List Reg)
    (hp : ∀ x y, P x y → ∀ r ∈ rs, x.gpr r = y.gpr r)
    {hint : VG.Taint.Hint VG.Arm.Taint.T}
    (hc : ((VG.Arm.taint.check (VG.Arm.Taint.ofRegs rs) c hint).map
      fun t => (RegSet.ofList out).subset t.regs) = some true) :
    CT P c (fun x y => ∀ r ∈ out, x.gpr r = y.gpr r) := by
  intro x y tx ty u v h ex ey
  obtain ⟨tau, ht, ho⟩ := Option.map_eq_some_iff.mp hc
  have ha : VG.Arm.Taint.Agree (VG.Arm.Taint.ofRegs rs) x y := VG.Arm.Taint.agree_ofRegs (hp x y h)
  obtain ⟨he, hf⟩ := VG.Taint.check_sound ht ha ex ey
  exact ⟨he, fun r hr => hf.rf.1 r (RegSet.mem_of_subset ho (RegSet.mem_ofList.mpr hr))⟩

theorem ctBoth {P F : State → Prop} {c : Prog isa}
    (hc : CT (fun x y => P x ∧ P y) c (fun _ _ => True))
    (hw : ∀ s, P s → WP isa c s F) : CT (fun x y => P x ∧ P y) c (fun x y => F x ∧ F y) :=
  (hc.wp (fun x y h => ⟨hw x h.1, hw y h.2⟩)).mono (fun _ _ h => h) (fun _ _ h => h.2)

theorem ctBlockAppend {P R Q : State → State → Prop} {xs ys : List Instr}
    (hx : CT P (.block xs) R) (hy : CT R (.block ys) Q) : CT P (.block (xs ++ ys)) Q := by
  intro x y tx ty u v hp ex ey
  have splitRun {s t : State} {tr : List Leak} (h : Exec isa (.block (xs ++ ys)) s tr t) :
      Exec isa (.seq (.block xs) (.block ys)) s tr t := by
    rw [Exec.block_iff, execBlock_append] at h
    obtain ⟨⟨a, ta⟩, ha, hb⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨⟨b, tb⟩, hb', he⟩ := Option.map_eq_some_iff.mp hb
    cases he
    exact .seq (.block ha) (.block hb')
  exact RelCT.seq hx hy _ _ _ _ _ _ hp (splitRun ex) (splitRun ey)

end VG.Proof.Ed25519.Arm
