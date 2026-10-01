import VerifiedGarbage.TCB.Axioms
import VerifiedGarbage.Proof.Sha3.AArch64.Sha3.Vector.Save
import VerifiedGarbage.Proof.Sha3.AArch64.Sha3.Vector.Load
import VerifiedGarbage.Proof.Sha3.AArch64.Sha3.Vector.Store
import VerifiedGarbage.Proof.Sha3.AArch64.Sha3.Vector.Restore
import VerifiedGarbage.Proof.Sha3.AArch64.Sha3.Vector.Lit

namespace VG.Proof.Sha3.AArch64.Sha3.Vector

open VG VG.AArch64
open VG.Impl.Sha3.AArch64.Sha3.Vector
open VG.Spec.Sha3 (stateAt keccakF)

/-- Saves do not alter the disjoint 200-byte Keccak state. -/
theorem state_frame (s₀ s : VG.AArch64.State) (hp : Pre s₀) (hptr : s.gpr .x0 = s₀.gpr .x0)
    (hf : Frame [⟨s₀.gpr .x1,512⟩] s₀.mem s.mem) :
    stateAt s.mem (s.gpr .x0) = stateAt s₀.mem (s₀.gpr .x0) := by
  rw [hptr]
  apply Vector.ext
  intro i hi
  simp only [stateAt,Vector.getElem_ofFn]
  exact hf.readW (VG.Proof.Sha3.lane_contains _ hi) (by simpa using hp.st_scr) (by decide)

theorem correct (s₀ : VG.AArch64.State) (hp : Pre s₀) :
    WP isa permute s₀ fun s' => s'.sp = s₀.sp ∧
      (∀ r ∈ VG.AArch64.preservedV, (s'.v r).extractLsb' 0 64 = (s₀.v r).extractLsb' 0 64) ∧
      VG.Proof.Sha3.permuteAArch64.post s₀ s' := by
  unfold permute
  rw [WP.block_append_iff,WP.block_append_iff,WP.block_append_iff,WP.block_append_iff]
  refine (save_ok s₀ hp).mono fun s₁ h₁ => ?_
  refine (load_ok s₁ (fun i hi => ?_) ?_).mono fun s₂ h₂ => ?_
  · rw [h₁.1.rd,h₁.1.wr,h₁.1.x0]
    exact hp.in_all (hp.in_wr (.inl rfl) (state_pair_contains s₀ hi))
  · rw [h₁.1.rd,h₁.1.wr,h₁.1.x0]
    exact hp.in_all (hp.lane_in (.inl rfl) (by decide : 24 < 25))
  · have ha : Lanes s₂ (stateAt s₀.mem (s₀.gpr .x0)) := by
      rw [state_frame s₀ s₁ hp h₁.1.x0 h₁.2.2.1] at h₂
      exact h₂.2.2
    refine (rounds_ok s₂ _ ha).mono fun s₃ h₃ => ?_
    have p₃ := h₁.1.trans (h₂.1.trans h₃.1.ptrs)
    have m₃ : s₃.mem = s₁.mem := h₃.1.mem.trans h₂.2.1
    refine (store_ok s₃ _ h₃.2 (fun i hi => ?_) ?_).mono fun s₄ h₄ => ?_
    · rw [p₃.wr,p₃.x0]
      exact hp.in_wr (.inl rfl) (state_pair_contains s₀ hi)
    · rw [p₃.wr,p₃.x0]
      exact hp.lane_in (.inl rfl) (by decide : 24 < 25)
    · have p₄ := p₃.trans h₄.1
      have hs₄ : Saved s₀ s₄.mem := by
        intro i hi
        rw [h₄.2.1.read (scratch_contains s₀ hi) ?_ (by decide),m₃]
        · exact h₁.2.2.2 i hi
        · simpa only [List.mem_singleton,p₃.x0,forall_eq] using hp.st_scr.symm
      refine (restore_ok s₀ s₄ hs₄ p₄.x1 (fun i hi => ?_)).mono fun s' h₅ => ?_
      · rw [p₄.rd,p₄.wr,p₄.x1]
        exact hp.in_all (hp.in_wr (.inr rfl) (scratch_contains s₀ hi))
      · refine ⟨h₅.1.sp.trans p₄.sp,h₅.2,?_⟩
        change stateAt s'.mem (s₀.gpr .x0) = _
        rw [h₅.1.mem]
        simpa only [p₃.x0] using h₄.2.2

theorem permute_preserved : ∀ r ∈ preserved, ∀ i ∈ instrs permute, dstOf i ≠ some r := by
  have h : ((instrs permute).all fun i => preserved.all fun r => dstOf i != some r) = true := by
    rw [← Code.allInstrs_eq]
    lit_decide
  intro r hr i hi
  have hh := List.all_eq_true.mp (List.all_eq_true.mp h i hi) r hr
  simpa using hh

theorem permute_noCalls : permute.noCalls = true := by lit_decide
theorem permute_noFrames : permute.noFrames = true := by lit_decide

theorem permute_correct (s : VG.AArch64.State) (hs : VG.Proof.Sha3.permuteAArch64.pre s) :
    ∃ t s', Exec isa permute s t s' ∧ abiPreserved s s' ∧ VG.Proof.Sha3.permuteAArch64.post s s' := by
  obtain ⟨t,s',he,hsp,hv,hpost⟩ := correct s (pre_of s hs)
  exact ⟨t,s',he,⟨fun r hr => Exec.gpr (permute_preserved r hr) he (.inl permute_noCalls),hsp,hv⟩,hpost⟩

theorem permute_ct : ConstantTime isa VG.Proof.Sha3.permuteAArch64.pre VG.Proof.Sha3.permuteAArch64.pub permute := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0,.x1]) ?_ (by taint_decide)
  intro s₁ s₂ _ _ ⟨h1,h2,hsp⟩
  refine ⟨hsp,fun r hr => ?_⟩
  simp only [Taint.mem_ofRegs,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl <;> assumption

theorem permute_verified :
    Verified AArch64.target permute (Spec.Sha3.permuteContract AArch64.abi) :=
  Verified.of_correct permute_correct permute_ct (by
    sig_implies [Spec.Sha3.permuteContract,Spec.Sha3.permuteSig,VG.Proof.Sha3.permuteAArch64,
      AArch64.abi,AArch64.argRegs] [VG.Proof.Sha3.AArch64.satState] using VG.Proof.Sha3.AArch64.satState)

/-- Core and boundary instructions, excluding the emitted return. -/
theorem permute_instruction_count : (instrs permute).length = 1723 := by lit_decide

#assert_standard_axioms permute_verified

end VG.Proof.Sha3.AArch64.Sha3.Vector
