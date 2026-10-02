import VerifiedGarbage.Proof.Argon2.X86_64.FillSetupReset
import VerifiedGarbage.Proof.Argon2.X86_64.FillIterationsBody

/-! Initialization hands filling the reviewed dimensions and stable public frame words. -/

namespace VG.Proof.Argon2.X86_64.FillSetup

open VG VG.X86_64 VG.Spec.Argon2

structure Environment (p : Params) (s : State) : Prop where
  parameters : FillContext.Parameters p 0 0 0
  passesBound : p.passes < 2 ^ 32
  layout : FillKernel.Layout p s
  addressLayout : AddressCalls.Ready s
  reads : ∀ d ∈ [0, 8, 72, 112, 240], InRegions (s.rd ++ s.wr) (off (s.gpr .rbp) d) 8
  counterWrite : InRegions s.wr (off (s.gpr .rbp) 8) 8
  passWrite : InRegions s.wr (off (s.gpr .rbp) 0) 8
  matrixWork : (⟨FillKernel.matrix s, p.blocks * 1024⟩ : Region).Disjoint ⟨AddressCalls.work s, 8192⟩
  blocksWord : s.mem.readW (off (s.gpr .rbp) 240) 64 = BitVec.ofNat 64 p.blocks
  passesWord : s.mem.readW (off (s.gpr .rbp) 72) 64 = BitVec.ofNat 64 p.passes
  variantWord : s.mem.readW (off (s.gpr .rbp) 112) 64 = BitVec.ofNat 64 p.variant.code
  lanesWord : s.mem.readW (off (s.gpr .rbp) 184) 64 = BitVec.ofNat 64 p.lanes

theorem Environment.of_state {p : Params} {s t : State} (h : Environment p s)
    (bp : t.gpr .rbp = s.gpr .rbp) (sp : t.gpr .rsp = s.gpr .rsp)
    (mem : t.mem = s.mem) (rd : t.rd = s.rd) (wr : t.wr = s.wr) : Environment p t := by
  have base : FillKernel.matrix t = FillKernel.matrix s := by unfold FillKernel.matrix; rw [mem, bp]
  have work : AddressCalls.work t = AddressCalls.work s := by unfold AddressCalls.work; rw [mem, bp]
  refine ⟨h.parameters, h.passesBound, h.layout.of_preserved bp sp base work rd wr, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · constructor
    · rw [rd, wr, bp]; exact h.addressLayout.frameRead
    · rw [wr, work]; exact h.addressLayout.workWrite
    · rw [bp, work]; exact h.addressLayout.frameWork
    · rw [bp, sp]; exact h.addressLayout.frameStack
    · rw [sp, work]; exact h.addressLayout.stackWork
  · rw [rd, wr, bp]; exact h.reads
  · rw [wr, bp]; exact h.counterWrite
  · rw [wr, bp]; exact h.passWrite
  · rw [base, work]; exact h.matrixWork
  all_goals rw [mem, bp]
  · exact h.blocksWord
  · exact h.passesWord
  · exact h.variantWord
  · exact h.lanesWord

theorem Reset.header {p : Params} {s t : State} (h : Environment p s) (reset : Reset s t)
    (laneLength : t.gpr .r12 = BitVec.ofNat 64 p.laneLen)
    (segmentLength : t.gpr .r13 = BitVec.ofNat 64 p.segmentLen) : FillHeader.Ready p 0 0 0 t := by
  have bp := reset.regs .rbp (by decide)
  have sp := reset.regs .rsp (by decide)
  have base : FillKernel.matrix t = FillKernel.matrix s := reset.read 232 (by decide) (by decide)
  have work : AddressCalls.work t = AddressCalls.work s := reset.read 248 (by decide) (by decide)
  refine ⟨h.layout.of_preserved bp sp base work reset.rd reset.wr, ?_, ?_, ?_, ?_, ?_, laneLength,
    segmentLength, (reset.read 184 (by decide) (by decide)).trans h.lanesWord⟩
  · constructor
    · rw [reset.rd, reset.wr, bp]; exact h.addressLayout.frameRead
    · rw [reset.wr, work]; exact h.addressLayout.workWrite
    · rw [bp, work]; exact h.addressLayout.frameWork
    · rw [bp, sp]; exact h.addressLayout.frameStack
    · rw [sp, work]; exact h.addressLayout.stackWork
  · rw [reset.rd, reset.wr, bp]; exact h.reads
  · rw [reset.wr, bp]; exact h.counterWrite
  · refine ⟨(s.mem.readW (off (s.gpr .rbp) 8) 64).toNat, reset.pass, reset.lane, reset.slice,
      (reset.read 240 (by decide) (by decide)).trans h.blocksWord,
      (reset.read 72 (by decide) (by decide)).trans h.passesWord,
      (reset.read 112 (by decide) (by decide)).trans h.variantWord, ?_⟩
    rw [reset.read 8 (by decide) (by decide)]
    simp only [BitVec.ofNat_toNat, BitVec.setWidth_eq]
  · rw [base, work]; exact h.matrixWork

end VG.Proof.Argon2.X86_64.FillSetup
