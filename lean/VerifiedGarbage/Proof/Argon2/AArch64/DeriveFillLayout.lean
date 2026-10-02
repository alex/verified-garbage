import VerifiedGarbage.Proof.Argon2.AArch64.DeriveMemorySpace

/-! One reviewed allocation supplies all filling and address-generation ranges. -/

namespace VG.Proof.Argon2.AArch64.Derive

open VG VG.AArch64

theorem private_fill_layout {s t : State} (h : AbiEnvironment s)
    (prepared : PrivatePrepared (prologueState s) t) : FillKernel.Layout (abiParams s) t := by
  have space := private_memory_space h prepared
  rw [private_matrix_bytes h] at space
  refine ⟨?_, private_local_write prepared 16 8 (by decide), space.matrix,
    private_work_cover h prepared 5120 (by decide), ?_, space.frameMatrix.symm, ?_, ?_,
    private_frame_stack prepared 8 (by decide), ?_⟩
  · intro d hd
    have bounds : ∀ d ∈ [0, 16, 184, 232, 248], d + 8 ≤ 272 := by decide
    exact private_local_read prepared d 8 (bounds d hd)
  · have pointer : t.gpr .x24 = FillKernel.work t := by
      rw [private_scratch h prepared]; exact (private_words h prepared).work.symm
    rw [← pointer]
    exact space.matrixWork.sub_right (Region.sub_prefix (by decide))
  · exact (space.stackMatrix.sub_left (below_sub (by decide) (by decide))).symm
  · have pointer : t.gpr .x24 = FillKernel.work t := by
      rw [private_scratch h prepared]; exact (private_words h prepared).work.symm
    rw [← pointer]
    exact space.frameWork.sub_right (Region.sub_prefix (by decide))
  · have pointer : t.gpr .x24 = FillKernel.work t := by
      rw [private_scratch h prepared]; exact (private_words h prepared).work.symm
    rw [← pointer]
    exact (space.stackWork.sub_left (below_sub (by decide) (by decide))).sub_right
      (Region.sub_prefix (by decide))

theorem private_address_layout {s t : State} (h : AbiEnvironment s)
    (prepared : PrivatePrepared (prologueState s) t) : AddressCalls.Ready t := by
  have space := private_memory_space h prepared
  have pointer : t.gpr .x24 = AddressCalls.work t := by
    rw [private_scratch h prepared]; exact (private_words h prepared).work.symm
  refine ⟨private_local_read prepared 248 8 (by decide), private_work_cover h prepared 8192 (by decide),
    ?_, private_frame_stack prepared 8 (by decide), ?_⟩
  · rw [← pointer]; exact space.frameWork.sub_right (Region.sub_prefix (by decide))
  · rw [← pointer]
    exact (space.stackWork.sub_left (below_sub (by decide) (by decide))).sub_right (Region.sub_prefix (by decide))

theorem private_fill_environment {s t : State} (h : AbiEnvironment s)
    (prepared : PrivatePrepared (prologueState s) t) : FillSetup.Environment (abiParams s) t := by
  have space := private_memory_space h prepared
  have words := private_words h prepared
  have pointer : t.gpr .x24 = AddressCalls.work t := by
    rw [private_scratch h prepared]; exact words.work.symm
  rw [private_matrix_bytes h] at space
  refine ⟨?_, h.valid.2.2.2.1, private_fill_layout h prepared, private_address_layout h prepared, ?_,
    private_local_write prepared 8 8 (by decide), private_local_write prepared 0 8 (by decide),
    ?_, words.blocks, words.passes, words.kind, words.lanes⟩
  · refine ⟨h.valid.1, Nat.lt_trans h.valid.2.1 (by decide), h.valid.2.2.2.2.1,
      h.valid.2.2.2.2.2.1, by decide, h.valid.1, by decide⟩
  · intro d hd
    have bounds : ∀ d ∈ [0, 8, 72, 112, 240], d + 8 ≤ 272 := by decide
    exact private_local_read prepared d 8 (bounds d hd)
  · rw [← pointer]; exact space.matrixWork.sub_right (Region.sub_prefix (by decide))

end VG.Proof.Argon2.AArch64.Derive
