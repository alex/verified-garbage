import VerifiedGarbage.Proof.Rc2.X86_64.Sse2Vector
import VerifiedGarbage.Proof.Rc2.RestoreMemory
import VerifiedGarbage.Proof.Rc2.Word

/-! # Reducing a scan and restoring its temporary memory -/

namespace VG.Proof.Rc2.X86_64.Sse2

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.Rc2.X86_64

theorem reduceOr_ok (s : State) :
    ∃ s', runBlock isa Sse2.reduceOr s = some s' ∧
      s'.xmm .xmm1 = reduceValue (s.xmm .xmm1) ∧
      KeepX [] [.xmm1, .xmm3] s s' := by
  refine ⟨_, by
    simp (config := {decide := true}) only [Sse2.reduceOr, List.flatMap_cons,
      List.flatMap_nil, List.cons_append, List.nil_append, runBlock_cons,
      runStep_some, runBlock_nil, exec, XOp.exec, xmm_setXmm_self, xmm_setXmm_of_ne]
    rfl, ?_⟩
  constructor
  · simp (config := {decide := true}) only [xmm_setXmm_self,
      XBinOp.eval, XShiftOp.eval]
    rfl
  · constructor
    · constructor
      · intro r _; simp only [gpr_setXmm]
      · simp only [mem_setXmm]
      · simp only [rd_setXmm]
      · simp only [wr_setXmm]
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp only [xmm_setXmm_of_ne _ _ hr.1, xmm_setXmm_of_ne _ _ hr.2]

theorem read64_word (m : Mem) (p : Addr) :
    (m.readW p 64).setWidth 16 = m.readW p 16 := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [Mem.readW, BitVec.getLsbD_setWidth, decide_eq_true hj, decide_eq_true (by omega : j < 64), Bool.true_and]
  rw [getLsbD_read _ _ (by omega), getLsbD_read _ _ (by omega)]

theorem stored_word (m : Mem) (p : Addr) (v : BitVec 128) :
    (m.writeW p v).readW p 64 &&& 65535 = (word v 0).setWidth 64 := by
  rw [maskWord, read64_word]
  have he := readW_writeW128_16 m p v (j := 0) (by decide)
  change (m.writeW p v).readW (p + 0#64) 16 = word v 0 at he
  rw [BitVec.add_zero] at he
  rw [he]

theorem finishTail_ok (s : State) (scratch : Reg) (hs : scratch ≠ .rax)
    (hread : InRegions (s.rd ++ s.wr) (s.gpr scratch + BitVec.ofNat 64 64) 8)
    (hwrite : InRegions s.wr (s.gpr scratch + BitVec.ofNat 64 64) 16)
    (hrestore : s.xmm .xmm8 = s.mem.readW (s.gpr scratch + BitVec.ofNat 64 64) 128) :
    ∃ s', runBlock isa
      [.movdquStore (memOp scratch 64) .xmm1, .mov .rax (.mem (memOp scratch 64)),
       .alu .and .rax (.imm 65535), .movdquStore (memOp scratch 64) .xmm8] s = some s' ∧
      s'.gpr .rax = (word (s.xmm .xmm1) 0).setWidth 64 ∧ Keep [.rax] s s' := by
  refine ⟨_, by
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc,
      State.store128, State.load64, State.ea, memOp, offset_nat, gpr_setReg_of_ne _ _ hs,
      gpr_arithFlags, gpr_setReg_self, xmm_setReg, xmm_arithFlags,
      wr_setReg, wr_arithFlags, hread, hwrite, ite_true, Option.bind_some, Option.map_some]
    rfl, ?_⟩
  constructor
  · simp only [gpr_setReg_self]
    change (s.mem.writeW _ (s.xmm .xmm1)).readW _ 64 &&&
      (65535#32).signExtend 64 = _
    rw [show (65535#32).signExtend 64 = (65535 : BitVec 64) by decide]
    exact stored_word _ _ _
  · constructor
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      simp only [gpr_setReg_of_ne _ _ hr, gpr_arithFlags]
    · simp only [mem_setReg, mem_arithFlags, hrestore]
      exact restore128 _ _ _
    · simp only [rd_setReg, rd_arithFlags]
    · rfl


end VG.Proof.Rc2.X86_64.Sse2
