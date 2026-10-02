import VerifiedGarbage.Impl.Argon2.AArch64.MemoryInit
import VerifiedGarbage.Proof.Argon2.AArch64.Instructions

/-! Public pointer advances and lane countdowns. -/
namespace VG.Proof.Argon2.AArch64.MemoryInit
open VG VG.AArch64

structure Advanced (s t : State) : Prop where
  destination : t.gpr .x22 = s.gpr .x22 + 1024
  other : ∀ r, r ≠ .x22 → r ≠ .x12 → r ≠ .x15 → t.gpr r = s.gpr r
  mem : t.mem = s.mem
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp

theorem advance_ok (s : State) :
    WP isa (.block [Impl.Argon2.AArch64.Instructions.addi .x22 1024].flatten) s (Advanced s) := by
  refine (Instructions.addi_ok s .x22 1024 (by decide) (by decide) (by decide)).mono ?_
  rintro t ⟨value, k⟩
  refine ⟨value, fun r h1 h2 h3 => k.regs r ?_, k.mem, k.rd, k.wr, k.sp⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
  exact ⟨h1,h2,h3⟩

structure LaneEnd (s t : State) : Prop where
  destination : t.gpr .x22 = s.gpr .x22 + s.gpr .x21 - 1024
  lane : t.gpr .x20 = s.gpr .x20 + 1
  remaining : t.gpr .x23 = s.gpr .x23 - 1
  flag : t.gpr .x15 = s.gpr .x23 - 1
  other : ∀ r, r ≠ .x22 → r ≠ .x20 → r ≠ .x23 → r ≠ .x12 → r ≠ .x15 → t.gpr r = s.gpr r
  mem : t.mem = s.mem
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp

theorem laneEnd_ok (s : State) :
    WP isa (.block [Impl.Argon2.AArch64.Instructions.add .x22 .x21,
      Impl.Argon2.AArch64.Instructions.subi .x22 1024,
      Impl.Argon2.AArch64.Instructions.addi .x20 1,
      Impl.Argon2.AArch64.Instructions.subi .x23 1].flatten) s (LaneEnd s) := by
  simp only [List.flatten_cons, List.flatten_nil, List.append_nil]
  rw [WP.block_append_iff]
  refine (Instructions.add_ok s .x22 .x21 (by decide)).mono ?_
  rintro a ⟨dstA, ka⟩
  rw [WP.block_append_iff]
  refine (Instructions.subi_ok a .x22 1024 (by decide) (by decide) (by decide)).mono ?_
  rintro b ⟨dstB, _, kb⟩
  rw [WP.block_append_iff]
  refine (Instructions.addi_ok b .x20 1 (by decide) (by decide) (by decide)).mono ?_
  rintro c ⟨laneC, kc⟩
  refine (Instructions.subi_ok c .x23 1 (by decide) (by decide) (by decide)).mono ?_
  rintro t ⟨remaining, flag, kt⟩
  have remainingC : c.gpr .x23 = s.gpr .x23 :=
    (kc.regs _ (by decide)).trans ((kb.regs _ (by decide)).trans (ka.regs _ (by decide)))
  refine ⟨?_, ?_, remaining.trans (congrArg (· - 1) remainingC),
    flag.trans (congrArg (· - 1) remainingC), ?_,
    kt.mem.trans (kc.mem.trans (kb.mem.trans ka.mem)),
    kt.rd.trans (kc.rd.trans (kb.rd.trans ka.rd)),
    kt.wr.trans (kc.wr.trans (kb.wr.trans ka.wr)),
    kt.sp.trans (kc.sp.trans (kb.sp.trans ka.sp))⟩
  · rw [kt.regs .x22 (by decide), kc.regs .x22 (by decide), dstB, dstA]; rfl
  · rw [kt.regs .x20 (by decide), laneC, kb.regs .x20 (by decide), ka.regs .x20 (by decide)]; rfl
  · intro r h1 h2 h3 h4 h5
    have hka : r ∉ [Reg.x22, .x15] := by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; exact ⟨h1,h5⟩
    have hkb : r ∉ [Reg.x22, .x12, .x15] := by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; exact ⟨h1,h4,h5⟩
    have hkc : r ∉ [Reg.x20, .x12, .x15] := by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; exact ⟨h2,h4,h5⟩
    have hkt : r ∉ [Reg.x23, .x12, .x15] := by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; exact ⟨h3,h4,h5⟩
    exact (kt.regs r hkt).trans ((kc.regs r hkc).trans ((kb.regs r hkb).trans (ka.regs r hka)))
end VG.Proof.Argon2.AArch64.MemoryInit
