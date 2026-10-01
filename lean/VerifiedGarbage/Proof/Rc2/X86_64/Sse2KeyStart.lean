import VerifiedGarbage.Proof.Rc2.X86_64.Sse2Vector
import VerifiedGarbage.Impl.Rc2.X86_64.Sse2KeyLookup

/-! # Initialization of SSE2 RC2 schedule lookup state -/

namespace VG.Proof.Rc2.X86_64.Sse2

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.Rc2.X86_64

theorem keyStart_ok (s : State) (scratch : Reg)
    (hread : InRegions (s.rd ++ s.wr) (s.gpr scratch + BitVec.ofNat 64 64) 16) :
    ∃ s', runBlock isa (Sse2.start scratch 63) s = some s' ∧
      s'.xmm .xmm0 = broadcast (((s.gpr .rax).setWidth 6).setWidth 8) ∧
      s'.xmm .xmm1 = 0#128 ∧ s'.xmm .xmm2 = Sse2.indices 0 ∧
      s'.xmm .xmm6 = Sse2.ones ∧ s'.xmm .xmm7 = Sse2.eights ∧
      s'.xmm .xmm8 = s.mem.readW (s.gpr scratch + BitVec.ofNat 64 64) 128 ∧
      Keep [.rax, .r10] s s' := by
  refine ⟨_, by
    simp (config := {decide := true}) only [Sse2.start, Sse2.loadConst,
      List.cons_append, List.nil_append,
      runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, XOp.exec,
      State.load128, State.ea, memOp, offset_nat, hread, ite_true, Option.bind_some,
      Option.map_some, gpr_setReg, gpr_setXmm, gpr_arithFlags,
      xmm_setReg, xmm_setXmm_self, xmm_setXmm_of_ne]
    rfl, ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp (config := {decide := true}) only [xmm_setXmm_self, xmm_setXmm_of_ne, xmm_setReg]
    rw [show (63#32).signExtend 64 = (63 : BitVec 64) by decide, maskIndex]
    apply ext_word
    intro i hi
    rw [broadcast, word_ofWords _ hi]
    simpa using broadcast_word (((s.gpr .rax).setWidth 6).setWidth 8) i hi
  · simp (config := {decide := true}) only [xmm_setXmm_self, xmm_setXmm_of_ne, xmm_setReg,
      XBinOp.eval, BitVec.xor_self]
  · simp (config := {decide := true}) only [xmm_setXmm_self, xmm_setXmm_of_ne, xmm_setReg]
  · simp (config := {decide := true}) only [xmm_setXmm_self, xmm_setXmm_of_ne, xmm_setReg]
  · simp only [xmm_setXmm_self]
    exact movq_const _
  · simp (config := {decide := true}) only [xmm_setXmm_of_ne, xmm_setReg,
      xmm_arithFlags, xmm_setXmm_self]
  · constructor
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp only [gpr_setXmm, gpr_setReg_of_ne _ _ hr.1, gpr_setReg_of_ne _ _ hr.2, gpr_arithFlags]
    · simp only [mem_setXmm, mem_setReg, mem_arithFlags]
    · simp only [rd_setXmm, rd_setReg, rd_arithFlags]
    · simp only [wr_setXmm, wr_setReg, wr_arithFlags]

end VG.Proof.Rc2.X86_64.Sse2
