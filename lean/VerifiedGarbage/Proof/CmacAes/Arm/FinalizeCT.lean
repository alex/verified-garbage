import VerifiedGarbage.Proof.CmacAes.Arm.FinalizeCorrect
import VerifiedGarbage.Proof.CmacAes.Arm.UpdateCT

/-!
# AES-CMAC on ARMv7: `vg_cmac_aes_finalize` is constant time

Untrusted: everything here is checked by Lean. The code before the call is
checked by the taint analysis, from the public arguments (its branches and
the copy loop depend only on `last_len`), the call of `vg_aes_ctr32`, in its
frame, is constant time by its own proof (`ctr_rel`), its arguments pinned
by the correctness proof (`FMid`), and the restore after it by the taint
analysis again, from `r5` (the scratch buffer).
-/

namespace VG.Proof.CmacAes.Arm

open VG VG.Arm VG.Impl.CmacAes.Arm

/-- The restore after the call. -/
abbrev finEnd : List Instr := [.ldr .r4 .r5 2064, .ldr .lr .r5 2072, .ldr .r5 .r5 2068]

theorem finalize_rel {s₀ s₀' : State} (h0 : finalizeArm.pre s₀) (h0' : finalizeArm.pre s₀')
    (hq : finalizeArm.pub s₀ s₀') :
    RelCT isa (fun a b => a = s₀ ∧ b = s₀') finalize fun _ _ => True := by
  obtain ⟨q₀, q₁, q₂, q₃, q₄, q₅, q₆⟩ := hq
  have hp := FPre.of h0
  have hp' := FPre.of h0'
  have eW : W s₀' = W s₀ := q₁.symm
  have eR : R s₀' = R s₀ := by rw [R, R, q₂]
  have eSt : St s₀' = St s₀ := q₃.symm
  have eS : S s₀' = S s₀ := q₆.symm
  obtain ⟨_, hA⟩ : ∃ h, (taint.check (argTaint [.r0, .r1, .r2, .r3] 8) finPre h).isSome = true :=
    ⟨_, by taint_decide⟩
  obtain ⟨_, hB⟩ : ∃ h, (taint.check (Taint.ofRegs [.r5]) (.block finEnd) h).isSome = true :=
    ⟨_, by taint_decide⟩
  have wfA : ∀ {s : State}, FPre s →
      s.sp.toNat + 8 ≤ 2 ^ 32 ∧ ∀ r ∈ s.wr, Region.Disjoint ⟨State.addr s.sp, 8⟩ r := fun {s} h => by
    have e : (⟨State.addr s.sp, 8⟩ : Region) = argsR s := by simp [stackArgAddr]
    refine ⟨h.sp_fit, ?_⟩
    rw [e, h.wr]
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · exact h.st_args.symm
    · exact h.scr_args.symm
  have a := rel_agree (F := fun s => s = s₀) (F' := fun s => s = s₀') (G := FMid s₀) (G' := FMid s₀')
    (argTaint [.r0, .r1, .r2, .r3] 8)
    (fun s s' e e' => by
      subst e e'
      refine agree_argTaint (fun r hr => ?_) q₀ (wfA hp) (wfA hp')
        (argMem_of (j := 2) q₀ hp.sp_fit fun i hi => ?_)
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl <;> assumption
      · rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl
        · exact q₅
        · exact q₆) ⟨_, hA⟩
    (fun s e => by rw [e]; exact finPre_wp hp) (fun s e => by rw [e]; exact finPre_wp hp')
  have c := rel_wp (F := FMid s₀) (F' := FMid s₀') (G := fun s => s.gpr .r5 = S s₀)
    (G' := fun s => s.gpr .r5 = S s₀')
    (ctr_rel (sp₀ := s₀.sp) fun s₁ s₂ h =>
      ⟨h.1.pre, by have := h.2.pre; rwa [eW, eS, eSt, eR] at this, h.1.sp, h.2.sp.trans q₀.symm⟩)
    (fun _ h => WP.mono (ctr_call h.pre) fun _ hc => by rw [hc.saved .r5 (by simp [preserved]) (by decide), h.r5])
    (fun _ h => WP.mono (ctr_call h.pre) fun _ hc => by rw [hc.saved .r5 (by simp [preserved]) (by decide), h.r5])
  have b := RelCT.taint (A := taint) (P := fun s₁ s₂ => s₁.gpr .r5 = S s₀ ∧ s₂.gpr .r5 = S s₀')
    (Taint.ofRegs [.r5]) (fun s₁ s₂ h => Taint.agree_ofRegs fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      subst hr; rw [h.1, h.2, eS]) hB
  exact a.seq (c.seq b)

theorem finalize_ct : ConstantTime isa finalizeArm.pre finalizeArm.pub finalize :=
  fun _ _ _ _ _ _ h₁ h₂ hq e₁ e₂ => (finalize_rel h₁ h₂ hq _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

end VG.Proof.CmacAes.Arm
