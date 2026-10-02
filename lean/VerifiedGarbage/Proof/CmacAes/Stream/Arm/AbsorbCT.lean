import VerifiedGarbage.Proof.CmacAes.Stream.Arm.AbsorbCorrect
import VerifiedGarbage.Proof.Framework.Arm.ArgTaint

/-!
# Streaming AES-CMAC on ARMv7: `vg_cmac_aes_absorb` is constant time

The taint analysis does not analyse frames, so two runs from states that agree
on the public arguments are related piece by piece (`RelCT`): the taint
analysis covers the code between the calls, from the public arguments for
`absorbPre` and from the registers the correctness proof pins to values of the
public arguments afterwards (`AAfter₁`, `AAfter₂`), and each call of
`vg_cmac_aes_update`, in its frame, is constant time by its own proof
(`upd_rel`).
-/

namespace VG.Proof.CmacAes.Stream.Arm

open VG VG.Arm VG.Impl.CmacAes.Stream.Arm

/-- The stack arguments of a state satisfying the precondition, for the
taint analysis. -/
theorem APre.wfA {s₀ : State} {St D S : BitVec 32} {L R : Nat} (hp : APre s₀ St D S L R) :
    s₀.sp.toNat + 12 ≤ 2 ^ 32 ∧ ∀ r ∈ s₀.wr, Region.Disjoint ⟨State.addr s₀.sp, 12⟩ r := by
  have e : (⟨State.addr s₀.sp, 12⟩ : Region) = ⟨stackArgAddr s₀ 0, 12⟩ := by simp [stackArgAddr]
  refine ⟨hp.spf, ?_⟩
  rw [e, hp.wr]
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl)
  · exact hp.a_st
  · exact hp.a_s

theorem absorb_rel {s₀ s₀' : State} (h0 : absorbArm.pre s₀) (h0' : absorbArm.pre s₀')
    (hq : absorbArm.pub s₀ s₀') :
    RelCT isa (fun a b => a = s₀ ∧ b = s₀') absorb fun _ _ => True := by
  obtain ⟨q1, q2, q3, q4, q5, q6, q7, q8⟩ := hq
  have hp := APre.of h0
  have hp' : APre s₀' (s₀.gpr .r0) (stackArg s₀ 0) (stackArg s₀ 2) (stackArg s₀ 1).toNat (s₀.gpr .r1).toNat := by
    rw [q2, q3, q6, q7, q8]; exact APre.of h0'
  have hc : (countArm s₀').toNat = (countArm s₀).toNat := by simp only [countArm, q4, q5]
  have wf := hp.wfA
  have wf' := hp'.wfA
  generalize s₀.gpr .r0 = St at hp hp'
  generalize stackArg s₀ 0 = D at hp hp'
  generalize stackArg s₀ 2 = S at hp hp'
  generalize (stackArg s₀ 1).toNat = L at hp hp'
  generalize (s₀.gpr .r1).toNat = R at hp hp'
  obtain ⟨_, hA⟩ : ∃ h, (taint.check (argTaint [.r0, .r1, .r2, .r3] 12) absorbPre h).isSome = true :=
    ⟨_, by taint_decide⟩
  obtain ⟨_, hB⟩ : ∃ h, (taint.check (Taint.ofRegs [.r4, .r5, .r6, .r7, .r10]) chain2 h).isSome = true :=
    ⟨_, by taint_decide⟩
  obtain ⟨_, hC⟩ : ∃ h, (taint.check (Taint.ofRegs [.r4, .r6, .r7, .r8, .r10]) absorbPost h).isSome = true :=
    ⟨_, by taint_decide⟩
  have a := rel_agree (F := fun s => s = s₀) (F' := fun s => s = s₀') (G := AMid₁ s₀ St D S L R)
    (G' := AMid₁ s₀' St D S L R) (argTaint [.r0, .r1, .r2, .r3] 12)
    (fun s s' e e' => by
      subst e e'
      refine agree_argTaint (fun r hr => ?_) q1 wf wf' (argMem_of (j := 3) q1 hp.spf fun i hi => ?_)
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl <;> assumption
      · rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl
        · exact q6
        · exact q7
        · exact q8) ⟨_, hA⟩
    (fun s e => by rw [e]; exact absorbPre_wp hp) (fun s e => by rw [e]; exact absorbPre_wp hp')
  have c₁ := rel_wp (F := AMid₁ s₀ St D S L R) (F' := AMid₁ s₀' St D S L R) (G := AAfter₁ s₀ St D S L)
    (G' := AAfter₁ s₀' St D S L)
    (upd_rel (sp₀ := s₀.sp) fun _ _ h => ⟨h.1.args, by rw [← hc]; exact h.2.args, h.1.sp, h.2.sp.trans q1.symm⟩)
    (fun _ h => call1_after h) (fun _ h => call1_after h)
  have m := rel_agree (F := AAfter₁ s₀ St D S L) (F' := AAfter₁ s₀' St D S L)
    (G := fun s => ∃ m, AMid₂ s₀ St D S L R m s) (G' := fun s => ∃ m, AMid₂ s₀' St D S L R m s)
    (Taint.ofRegs [.r4, .r5, .r6, .r7, .r10])
    (fun s s' h h' => by
      refine Taint.agree_ofRegs fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl
      · rw [h.r4, h'.r4]
      · rw [h.r5, h'.r5, q3]
      · rw [h.r6, h'.r6, hc]
      · rw [h.r7, h'.r7, hc]
      · rw [h.r10, h'.r10]) ⟨_, hB⟩
    (fun s h => WP.mono (chain2_mid hp h) fun _ h => ⟨_, h⟩)
    (fun s h => WP.mono (chain2_mid hp' h) fun _ h => ⟨_, h⟩)
  have c₂ := rel_wp (F := fun s => ∃ m, AMid₂ s₀ St D S L R m s) (F' := fun s => ∃ m, AMid₂ s₀' St D S L R m s)
    (G := AAfter₂ s₀ St D S L) (G' := AAfter₂ s₀' St D S L)
    (upd_rel (sp₀ := s₀.sp) fun _ _ ⟨⟨_, h₁⟩, ⟨_, h₂⟩⟩ =>
      ⟨h₁.args, by rw [← hc]; exact h₂.args, h₁.sp, h₂.sp.trans q1.symm⟩)
    (fun _ ⟨_, h⟩ => call2_after h) (fun _ ⟨_, h⟩ => call2_after h)
  have p := RelCT.taint (A := taint) (P := fun a b => AAfter₂ s₀ St D S L a ∧ AAfter₂ s₀' St D S L b)
    (Taint.ofRegs [.r4, .r6, .r7, .r8, .r10]) (fun a b h => by
      refine Taint.agree_ofRegs fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl
      · rw [h.1.r4, h.2.r4]
      · rw [h.1.r6, h.2.r6, hc]
      · rw [h.1.r7, h.2.r7, hc]
      · rw [h.1.r8, h.2.r8, hc]
      · rw [h.1.r10, h.2.r10]) hC
  exact a.seq (c₁.seq (m.seq (c₂.seq p)))

theorem absorb_ct : ConstantTime isa absorbArm.pre absorbArm.pub absorb :=
  fun _ _ _ _ _ _ h₁ h₂ hq e₁ e₂ => (absorb_rel h₁ h₂ hq _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

end VG.Proof.CmacAes.Stream.Arm
