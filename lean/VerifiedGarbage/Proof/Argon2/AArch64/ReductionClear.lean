import VerifiedGarbage.Proof.Argon2.AArch64.ReductionLoopState
import VerifiedGarbage.Proof.Argon2.AArch64.ClearBlock

/-! Clear only block zero, preserving the original last blocks in the matrix. -/

namespace VG.Proof.Argon2.AArch64.ReductionState

open VG VG.AArch64 VG.Spec.Argon2

structure Cleared (s t : State) (p : Params) (memory : Array Block) : Prop where
  ready : Ready p t
  represented : Represents p memory zeroBlock t
  base : matrix t = matrix s
  keeps : CopyKeeps s t
  frame : Frame [⟨matrix s, 1024⟩] s.mem t.mem
  sp : t.sp = s.sp

theorem clear_ok (s : State) (p : Params) (h : Ready p s)
    (dest : s.gpr .x0 = matrix s) (memory : Array Block)
    (represented : Proof.Argon2.Represents s.mem (matrix s) p.blocks memory) :
    WP isa Impl.Argon2.AArch64.ClearBlock.code s (Cleared s · p memory) := by
  have write : Covers [⟨s.gpr .x0, 1024⟩] s.wr := by rw [dest]; exact h.accumulator_cover
  refine (ClearBlock.code_ok s write).mono ?_
  rintro t ⟨zero, frame, keeps, mx⟩
  rw [dest] at frame zero
  have bp := keeps.1 .x19 (by decide) (by decide)
  have nonempty := Proof.Argon2.lastIndex_bounds p h.positive h.minimum 0 h.positive
  have metadata (d : Nat) (bound : d + 8 ≤ 272) :
      t.mem.readW (off (t.gpr .x19) d) 64 = s.mem.readW (off (s.gpr .x19) d) 64 := by
    rw [bp]
    exact frame.readW (r := ⟨s.gpr .x19, 272⟩) (Offset.contains_base _ bound (by omega))
      (by intro r hr; simp only [List.mem_singleton] at hr; subst r
          exact h.frame.symm.sub_right (Region.sub_prefix (by omega))) (by decide)
  have base : matrix t = matrix s := metadata 232 (by decide)
  refine ⟨?_, ?_, base, keeps, frame, mx⟩
  · refine ⟨h.positive, h.minimum, h.bound, ?_, ?_, ?_, (keeps.1 .x20 (by decide) (by decide)).trans h.length⟩
    · rw [keeps.2.1, keeps.2.2, bp]; exact h.read
    · rw [base, keeps.2.2]; exact h.write
    · rw [base, bp]; exact h.frame
  · constructor
    · rw [base]; exact zero
    · intro lane active
      rw [base]
      apply Eq.trans _ (represented.block _ (Proof.Argon2.lastIndex_bounds p h.positive h.minimum lane active).2)
      apply FillCompress.block_frame frame
      intro r hr
      simp only [List.mem_singleton] at hr
      subst r
      have bounds := Proof.Argon2.lastIndex_bounds p h.positive h.minimum lane active
      simpa only [Proof.Argon2.matrixCell, Nat.zero_mul, BitVec.add_zero] using
        Proof.Argon2.matrixCell_disjoint (matrix s) p.blocks (Proof.Argon2.lastIndex p lane) 0 h.bound
          bounds.2 (by omega) (by omega)

theorem Cleared.frame_word {p : Params} {s t : State} {memory : Array Block}
    (ready : Ready p s) (done : Cleared s t p memory) (d : Nat) (bound : d + 8 ≤ 272) :
    t.mem.readW (off (t.gpr .x19) d) 64 = s.mem.readW (off (s.gpr .x19) d) 64 := by
  rw [done.keeps.1 .x19 (by decide) (by decide)]
  exact done.frame.readW (r := ⟨s.gpr .x19, 272⟩) (Offset.contains_base _ bound (by omega))
    (by intro r hr; simp only [List.mem_singleton] at hr; subst r
        exact ready.frame.symm.sub_right (Region.sub_prefix (by
          have nonempty := Proof.Argon2.lastIndex_bounds p ready.positive ready.minimum 0 ready.positive
          omega))) (by decide)

end VG.Proof.Argon2.AArch64.ReductionState
