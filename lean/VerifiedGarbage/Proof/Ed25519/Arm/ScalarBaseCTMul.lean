import VerifiedGarbage.Proof.Ed25519.Arm.ScalarBaseCTInit

/-! Public initialization and synchronized batches prove scalar multiplication constant time. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm

materialize_code mulInit16CT := pointMultiplyInitCT 16
materialize_code mulInit32CT := pointMultiplyInitCT 32

def MulCTPre (b ptr : BitVec 32) (count scalar : Nat) (s : State) : Prop :=
  Ctx b s ∧ AllLim s.mem b ∧ MulInput b ptr count scalar s ∧ env s.mem b 16 = Spec.Ed25519.d

theorem pointMultiply_ct (b ptr : BitVec 32) (count scalar₁ scalar₂ : Nat)
    (hn : count = 16 ∨ count = 32) :
    CT (fun x y => MulCTPre b ptr count scalar₁ x ∧ MulCTPre b ptr count scalar₂ y)
      (pointMultiply count) (fun _ _ => True) := by
  have hn0 : 0 < count := by rcases hn with rfl | rfl <;> decide
  have hi : CT (fun x y => MulCTPre b ptr count scalar₁ x ∧ MulCTPre b ptr count scalar₂ y)
      (pointMultiplyInitCT count) (fun _ _ => True) := by
    have hr : ∀ x y, (MulCTPre b ptr count scalar₁ x ∧ MulCTPre b ptr count scalar₂ y) →
        ∀ r ∈ ([.r0] : List Reg), x.gpr r = y.gpr r := by
      intro x y h r hr
      rw [List.mem_singleton] at hr
      subst r
      exact h.1.1.r0.trans h.2.1.r0.symm
    rcases hn with rfl | rfl
    · exact ctRegs [.r0] hr (by taint_decide)
    · exact ctRegs [.r0] hr (by taint_decide)
  intro x y tx ty u v h ex ey
  cases ex with
  | seq ep ex =>
    cases ex with
    | seq ec ex =>
      cases ex with
      | seq ei el =>
        cases ey with
        | seq fp ey =>
          cases ey with
          | seq fc ey =>
            cases ey with
            | seq fi fl =>
              have exi := Exec.seq ep (Exec.seq ec ei)
              have eyi := Exec.seq fp (Exec.seq fc fi)
              have ht := (hi _ _ _ _ _ _ h exi eyi).1
              obtain ⟨_, a, ea, ha⟩ := pointMultiplyInitCT_ok h.1.1 h.1.2.1 count scalar₁ h.1.2.2.1 hn0 h.1.2.2.2
              obtain ⟨_, b', eb, hb⟩ := pointMultiplyInitCT_ok h.2.1 h.2.2.1 count scalar₂ h.2.2.2.1 hn0 h.2.2.2.2
              obtain ⟨_, rfl⟩ := Exec.det exi ea
              obtain ⟨_, rfl⟩ := Exec.det eyi eb
              have hl := (pointMulLoop_ct _ _ b ptr count scalar₁ scalar₂ _ _ count _ _ _ _ _ _
                ⟨ha, hb⟩ el fl).1
              exact ⟨by simpa only [List.append_assoc] using congrArg₂ (fun (a b : List Leak) => a ++ b) ht hl, trivial⟩

end VG.Proof.Ed25519.Arm
