import VerifiedGarbage.Proof.Argon2.AArch64.FillIterationsFrame

/-! A complete pass retains the matrix and advances its public iteration counter. -/

namespace VG.Proof.Argon2.AArch64.FillIterations

open VG VG.AArch64 VG.Spec.Argon2

structure Ready (p : Params) (pass : Nat) (s : State) : Prop where
  filling : FillIteration.Ready p pass s
  passesBound : p.passes < 2 ^ 32
  passWrite : InRegions s.wr (off (s.gpr .x19) 0) 8

structure Done (s t : State) (p : Params) (pass : Nat) (state : FillState) : Prop where
  represented : Proof.Argon2.Represents t.mem (FillKernel.matrix t) p.blocks (fillPass p state pass).memory
  matrix : FillKernel.matrix t = FillKernel.matrix s
  work : AddressCalls.work t = AddressCalls.work s
  header : FillHeader.Ready p (pass + 1) p.lanes 4 t
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  frame : Frame (writes s p) s.mem t.mem
  sp : t.sp = s.sp
  regs : ∀ r ∈ FillCompress.loopRegs, r ≠ .x24 → r ≠ .x22 → r ≠ .x23 → t.gpr r = s.gpr r
  cf : eval (.nonzero .x .x14) t = some (decide (pass + 1 < p.passes))
  next : pass + 1 < p.passes → Ready p (pass + 1) t

theorem body_ok (s : State) (p : Params) (pass : Nat) (h : Ready p pass s) (state : FillState)
    (represented : Proof.Argon2.Represents s.mem (FillKernel.matrix s) p.blocks state.memory) :
    WP isa Impl.Argon2.AArch64.FillIterations.body s (Done s · p pass state) := by
  unfold Impl.Argon2.AArch64.FillIterations.body
  refine WP.seq ((FillIteration.code_ok s p pass h.filling state represented).mono ?_)
  intro a filled
  have write : InRegions a.wr (off (a.gpr .x19) 0) 8 := by
    rw [filled.wr, filled.regs .x19 (by simp [FillCompress.loopRegs]) (by decide) (by decide) (by decide)]
    exact h.passWrite
  obtain ⟨old, words⟩ := filled.header.words
  have passBound := h.filling.parameters.passBound
  have added : (BitVec.ofNat 64 pass + 1 : Addr) = BitVec.ofNat 64 (pass + 1) := by
    rw [BitVec.ofNat_add]; rfl
  have left : (a.mem.readW (off (a.gpr .x19) 0) 64 + 1).toNat < 2 ^ 63 := by
    rw [words.passWord, added, ReferenceMap.word_nat (pass + 1) (by omega)]; omega
  have right : (a.mem.readW (off (a.gpr .x19) 72) 64).toNat < 2 ^ 63 := by
    rw [words.passesWord, ReferenceMap.word_nat p.passes (Nat.lt_trans h.passesBound (by decide))]
    exact Nat.lt_trans h.passesBound (by decide)
  refine (advance_ok a (filled.header.reads 0 (by simp)) write
    (filled.header.reads 72 (by simp)) left right).mono ?_
  intro t saved
  have header := saved.header filled.header
  have base : FillKernel.matrix t = FillKernel.matrix a := saved.read 232 (by decide) (by decide)
  have work : AddressCalls.work t = AddressCalls.work a := saved.read 248 (by decide) (by decide)
  refine ⟨saved.represents filled.header _ filled.represented, base.trans filled.matrix,
    work.trans filled.work, header, saved.rd.trans filled.rd, saved.wr.trans filled.wr,
    ?_, saved.sp.trans filled.sp, ?_, ?_, ?_⟩
  · have lastFrame := saved.outer_frame (p := p)
    rw [writes, filled.matrix, filled.work,
      filled.sp,
      filled.regs .x19 (by simp [FillCompress.loopRegs]) (by decide) (by decide) (by decide)] at lastFrame
    exact (filling_frame filled.frame).trans lastFrame
  · intro r hr bx sl ix
    have ne : r ∉ [Reg.x8, .x12, .x13, .x14, .x15] := by
      simp only [FillCompress.loopRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    exact (saved.regs r ne).trans (filled.regs r hr bx sl ix)
  · rw [saved.cf, words.passWord, words.passesWord, added, ReferenceMap.word_nat (pass + 1) (by omega),
      ReferenceMap.word_nat p.passes (Nat.lt_trans h.passesBound (by decide))]
  · intro active
    refine ⟨⟨{ h.filling.parameters with passBound := Nat.lt_trans active h.passesBound }, p.lanes, 4, header⟩,
      h.passesBound, ?_⟩
    rw [saved.wr, saved.regs .x19 (by decide)]; exact write

end VG.Proof.Argon2.AArch64.FillIterations
