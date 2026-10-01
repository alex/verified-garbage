import VerifiedGarbage.Proof.Ed25519.Arm.ScalarBaseCTFrom
import VerifiedGarbage.Proof.Ed25519.Arm.ScalarBaseEngine

/-! Initialization, secret scalar multiplication, and encoding have public traces. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm

def BaseCTPre (b p : BitVec 32) (s : State) : Prop :=
  Ctx b s ∧ s.gpr .r12 = p ∧ p.toNat + 32 ≤ 2 ^ 32 ∧
    (∀ i < 32, InRegions (s.rd ++ s.wr) (State.addr p + BitVec.ofNat 64 i) 1) ∧
    (⟨State.addr p, 32⟩ : Region).Disjoint ⟨State.addr b, 8192⟩

def basePrepareCT : Prog isa := .seq (.block initFields) (constPoint Spec.Ed25519.basePoint)

materialize_code basePrepareCT

theorem basePrepareCT_ok {s : State} {base ptr : BitVec 32} (h : BaseCTPre base ptr s) :
    WP isa basePrepareCT s (FromCTPre base ptr 16) := by
  obtain ⟨hc, hp, hfit, hr, hsep⟩ := h
  refine WP.seq (WP.mono (initFields_ok hc) fun a ⟨ak, al, _⟩ => ?_)
  refine WP.mono (fieldCode_ok (constPointOps Spec.Ed25519.basePoint) (ak.ctx hc) al)
    fun u ⟨uk, ul, _⟩ => ?_
  have ku := ak.trans uk
  refine ⟨ku.ctx hc, ul, (ku.rest.gpr _ (by decide)).trans hp, hfit, ?_, hsep⟩
  intro i hi
  rw [ku.rest.rd, ku.rest.wr]
  exact hr i hi

theorem scalarBaseEngine_ct (base ptr : BitVec 32) :
    CT (fun x y => BaseCTPre base ptr x ∧ BaseCTPre base ptr y)
      scalarBaseEngine (fun _ _ => True) := by
  have hp : CT (fun x y => BaseCTPre base ptr x ∧ BaseCTPre base ptr y)
      basePrepareCT (fun x y => FromCTPre base ptr 16 x ∧ FromCTPre base ptr 16 y) := by
    apply ctBoth
    · apply ctRegs [.r0] _ (by taint_decide)
      intro x y h r hr
      rw [List.mem_singleton] at hr
      subst r
      exact h.1.1.r0.trans h.2.1.r0.symm
    · exact fun _ h => basePrepareCT_ok h
  have hm := (pointFromScalar_ct base ptr 16 (.inl rfl)).wpDep (fun x y h =>
    ⟨pointFromScalar_ok h.1.1 h.1.2.1 h.1.2.2.1 16 (by decide) (by decide)
      h.1.2.2.2.1 h.1.2.2.2.2.1 h.1.2.2.2.2.2,
     pointFromScalar_ok h.2.1 h.2.2.1 h.2.2.2.1 16 (by decide) (by decide)
      h.2.2.2.2.1 h.2.2.2.2.2.1 h.2.2.2.2.2.2⟩)
  have hm' := hm.mono (fun _ _ h => h) (fun x y ⟨_, a, b, h, hx, hy⟩ =>
    And.intro (hx.1.ctx h.1.1).r0 (hy.1.ctx h.2.1).r0)
  have he : CT (fun (x y : State) => x.gpr .r0 = base ∧ y.gpr .r0 = base)
      pointEncode (fun _ _ => True) := by
    apply ctRegs [.r0] _ (by taint_decide)
    intro x y h r hr
    rw [List.mem_singleton] at hr
    subst r
    exact h.1.trans h.2.symm
  intro x y tx ty u v h ex ey
  cases ex with
  | seq ei ex =>
    cases ex with
    | seq ep em =>
      cases ey with
      | seq fi ey =>
        cases ey with
        | seq fp fm =>
          obtain ⟨ht, hh⟩ := hp _ _ _ _ _ _ h (Exec.seq ei ep) (Exec.seq fi fp)
          have hm := (RelCT.seq hm' he _ _ _ _ _ _ hh em fm).1
          exact ⟨by simpa only [List.append_assoc] using
            congrArg₂ (fun (a b : List Leak) => a ++ b) ht hm, trivial⟩

end VG.Proof.Ed25519.Arm
