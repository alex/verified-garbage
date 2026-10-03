import VerifiedGarbage.Proof.Argon2.X86_64.DeriveFillLayout

/-! Final lane reduction and H′ use the matrix and disjoint output/scratch allocations. -/

namespace VG.Proof.Argon2.X86_64.Derive

open VG VG.X86_64

theorem private_final_layout {s t : State} (h : AbiEnvironment s)
    (prepared : PrivatePrepared (prologueState s) t) : FinalOutput.Ready (abiParams s) t := by
  have words := private_words h prepared
  have separation := abi_separation h
  have environment := private_fill_environment h prepared
  have parameters := environment.parameters
  have blocks := Proof.Argon2.lastIndex_bounds (abiParams s) parameters.lanesPositive
    parameters.segment_bound.1 0 parameters.lanesPositive
  have minimum : 1024 ≤ (abiParams s).blocks * 1024 := by
    have positive : 1 ≤ (abiParams s).blocks := by omega
    simpa only [Nat.one_mul] using Nat.mul_le_mul_right 1024 positive
  have matrix := private_matrix_region h prepared
  have work : FinalOutput.work t = (abiWork s).base := words.work
  have output : (⟨FinalOutput.output t, (abiParams s).tagLen⟩ : Region) = abiOutput s := by
    change (⟨Initial.wordAt t 256, (abiParams s).tagLen⟩ : Region) = abiOutput s
    rw [words.output]; rfl
  have matrixMember : (abiMatrix s, true) ∈ abiBuffers s ++ [(abiArguments s, false)] := by
    simp only [abiBuffers, List.mem_append, List.mem_cons, true_or, or_true]
  have workMember : (abiWork s, true) ∈ abiBuffers s ++ [(abiArguments s, false)] := by
    simp only [abiBuffers, List.mem_append, List.mem_cons, true_or, or_true]
  have outputMember : (abiOutput s, true) ∈ abiBuffers s ++ [(abiArguments s, false)] := by
    simp only [abiBuffers, List.mem_append, List.mem_cons, true_or, or_true]
  have matrixWork : (⟨ReductionState.matrix t, 1024⟩ : Region).Disjoint ⟨FinalOutput.work t, 16384⟩ := by
    rw [work]
    apply Region.Disjoint.sub_left separation.matrixWork
    rw [← matrix]
    exact Region.sub_prefix minimum
  have stackMatrix : (below (t.gpr .rsp) 24).Disjoint ⟨ReductionState.matrix t, 1024⟩ := by
    apply Region.Disjoint.sub_right
      (private_stack_disjoint h prepared (abiMatrix s, true) matrixMember 24 (by decide))
    rw [← matrix]; exact Region.sub_prefix minimum
  refine ⟨by have tag := h.valid.2.2.2.2.2.2.1; omega, h.valid.2.2.2.2.2.2.2.1,
    ?_, words.tagLength, ?_, private_output_cover h prepared, ?_, matrixWork, ?_, stackMatrix, ?_, ?_⟩
  · intro d hd
    have bounds : ∀ d ∈ [232, 256, 264, 248], d + 8 ≤ 272 := by decide
    exact private_local_read prepared d 8 (bounds d hd)
  · intro p n ⟨region, member, contains⟩
    simp only [List.mem_singleton] at member; subst region
    have contained : Region.Contains ⟨FillKernel.matrix t, (abiParams s).blocks * 1024⟩ p n := by
      unfold Region.Contains at contains ⊢; exact Nat.le_trans contains minimum
    obtain ⟨r, hr, hc⟩ := private_matrix_cover h prepared p n ⟨_, List.mem_singleton_self _, contained⟩
    exact ⟨r, List.mem_append_right _ hr, hc⟩
  · rw [work]; exact private_work_member h prepared
  · rw [output, work]; exact separation.outputWork
  · rw [output]; exact private_stack_disjoint h prepared (abiOutput s, true) outputMember 24 (by decide)
  · rw [work]; exact private_stack_disjoint h prepared (abiWork s, true) workMember 24 (by decide)

end VG.Proof.Argon2.X86_64.Derive
