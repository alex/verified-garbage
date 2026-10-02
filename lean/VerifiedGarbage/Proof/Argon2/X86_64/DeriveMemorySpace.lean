import VerifiedGarbage.Proof.Argon2.X86_64.DeriveAllocations

/-! The signature's rounded block allocation supplies all initialization permissions. -/

namespace VG.Proof.Argon2.X86_64.Derive

open VG VG.X86_64

theorem private_matrix_bytes {s : State} (h : AbiEnvironment s) :
    1024 * ((abiParams s).lanes * (abiParams s).laneLen) = (abiParams s).blocks * 1024 := by
  rw [← Proof.Argon2.blocks_lanes (abiParams s) h.valid.1, Nat.mul_comm]

theorem private_memory_space {s t : State} (h : AbiEnvironment s)
    (prepared : PrivatePrepared (prologueState s) t) :
    MemoryInit.Space t (FillKernel.matrix t)
      (1024 * ((abiParams s).lanes * (abiParams s).laneLen)) := by
  have matrix := private_matrix_region h prepared
  have separation := abi_separation h
  have scratch := private_scratch h prepared
  have matrixMember : (abiMatrix s, true) ∈ abiBuffers s ++ [(abiArguments s, false)] := by
    simp only [abiBuffers, List.mem_append, List.mem_cons, true_or, or_true]
  have workMember : (abiWork s, true) ∈ abiBuffers s ++ [(abiArguments s, false)] := by
    simp only [abiBuffers, List.mem_append, List.mem_cons, true_or, or_true]
  rw [private_matrix_bytes h]
  refine ⟨private_matrix_cover h prepared, private_local_cover prepared 72 (by decide), ?_,
    ?_, ?_, ?_, (private_frame_stack prepared 24 (by decide)).symm, ?_, ?_, ?_⟩
  · rw [scratch]; exact private_work_member h prepared
  · rw [matrix]; exact private_frame_disjoint h prepared (abiMatrix s, true) matrixMember
  · rw [scratch]; exact private_frame_disjoint h prepared (abiWork s, true) workMember
  · rw [matrix, scratch]; exact separation.matrixWork
  · rw [matrix]; exact private_stack_disjoint h prepared (abiMatrix s, true) matrixMember 24 (by decide)
  · rw [scratch]; exact private_stack_disjoint h prepared (abiWork s, true) workMember 24 (by decide)
  · have blocks := Proof.Argon2.blocks_le_memory (abiParams s)
    have memoryBound := h.valid.2.2.2.2.2.1
    omega

end VG.Proof.Argon2.X86_64.Derive
