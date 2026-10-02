import VerifiedGarbage.Proof.Argon2.X86_64.ReduceLane

/-! Public loop metadata survives accumulator writes and register-only advancement. -/

namespace VG.Proof.Argon2.X86_64.ReductionState

open VG VG.X86_64 VG.Spec.Argon2

theorem Ready.of_state {p : Params} {s t : State} (h : Ready p s)
    (bp : t.gpr .rbp = s.gpr .rbp) (length : t.gpr .r12 = s.gpr .r12)
    (mem : t.mem = s.mem) (rd : t.rd = s.rd) (wr : t.wr = s.wr) : Ready p t := by
  have base : matrix t = matrix s := by unfold matrix; rw [mem, bp]
  refine ⟨h.positive, h.minimum, h.bound, ?_, ?_, ?_, length.trans h.length⟩
  · rw [rd, wr, bp]; exact h.read
  · rw [base, wr]; exact h.write
  · rw [base, bp]; exact h.frame

theorem Represents.of_state {p : Params} {s t : State} {memory : Array Block} {acc : Block}
    (h : Represents p memory acc s) (bp : t.gpr .rbp = s.gpr .rbp) (mem : t.mem = s.mem) :
    Represents p memory acc t := by
  have base : matrix t = matrix s := by unfold matrix; rw [mem, bp]
  constructor
  · rw [mem, base]; exact h.accumulator
  · rw [mem, base]; exact h.last

theorem frame_word {p : Params} {s t : State} {memory : Array Block} {acc : Block}
    (h : Ready p s) (done : ReduceLane.Done s t p memory acc) (d : Nat) (bound : d + 8 ≤ 272) :
    t.mem.readW (off (t.gpr .rbp) d) 64 = s.mem.readW (off (s.gpr .rbp) d) 64 := by
  rw [done.regs .rbp (by simp [calleeSaved])]
  exact done.frame.readW (r := ⟨s.gpr .rbp, 272⟩) (Offset.contains_base _ bound (by omega))
    (by intro r hr; simp only [List.mem_singleton] at hr; subst r
        exact h.frame.symm.sub_right (Region.sub_prefix (by
          have nonempty := Proof.Argon2.lastIndex_bounds p h.positive h.minimum 0 h.positive
          omega))) (by decide)

end VG.Proof.Argon2.X86_64.ReductionState
