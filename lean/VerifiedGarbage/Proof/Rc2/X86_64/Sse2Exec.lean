import VerifiedGarbage.Impl.Rc2.X86_64.Sse2Lookup
import VerifiedGarbage.Proof.Rc2.X86_64.Lookup
import VerifiedGarbage.Proof.Rc2.X86_64.Sse2Mask

/-! # Register-only SSE2 RC2 lookup steps -/

namespace VG.Proof.Rc2.X86_64.Sse2

open VG VG.X86_64 VG.X86_64.RegUpd

structure KeepX (regs : List Reg) (xregs : List XReg) (s s' : State) : Prop where
  keep : Keep regs s s'
  xmm : ∀ r, r ∉ xregs → s'.xmm r = s.xmm r

theorem KeepX.trans {rs : List Reg} {xs : List XReg} {s s' s'' : State}
    (h : KeepX rs xs s s') (h' : KeepX rs xs s' s'') : KeepX rs xs s s'' :=
  ⟨h.keep.trans h'.keep, fun r hr => (h'.xmm r hr).trans (h.xmm r hr)⟩

theorem loadConst_ok (s : State) (dst : XReg) (hd : dst ≠ .xmm5) (v : BitVec 128) :
    ∃ s', runBlock isa (Impl.Rc2.X86_64.Sse2.loadConst dst v) s = some s' ∧
      s'.xmm dst = v ∧ KeepX [.r10] [dst, .xmm5] s s' := by
  refine ⟨_, by
    simp only [Impl.Rc2.X86_64.Sse2.loadConst, runBlock_cons, runStep_some,
      runBlock_nil, exec, XOp.exec, gpr_setReg,
      gpr_setXmm, xmm_setReg, xmm_setXmm_self, xmm_setXmm_of_ne _ _ hd]
    rfl, ?_⟩
  constructor
  · simp only [xmm_setXmm_self]
    exact movq_const v
  · constructor
    · constructor
      · intro r hr
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        simp only [gpr_setXmm, gpr_setReg_of_ne _ _ hr]
      · simp only [mem_setXmm, mem_setReg]
      · simp only [rd_setXmm, rd_setReg]
      · simp only [wr_setXmm, wr_setReg]
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp only [xmm_setXmm_of_ne _ _ hr.1, xmm_setXmm_of_ne _ _ hr.2, xmm_setReg]

def selectValue (a b c v : BitVec 128) : BitVec 128 :=
  XBinOp.eval .pand
    (XShiftOp.eval .psraw (XBinOp.eval .psubw (a ^^^ b) c) 15) v

theorem select_ok (s : State) :
    ∃ s', runBlock isa Impl.Rc2.X86_64.Sse2.select s = some s' ∧
      s'.xmm .xmm1 = s.xmm .xmm1 |||
        selectValue (s.xmm .xmm0) (s.xmm .xmm2) (s.xmm .xmm6) (s.xmm .xmm4) ∧
      s'.xmm .xmm2 = XBinOp.eval .paddw (s.xmm .xmm2) (s.xmm .xmm7) ∧
      KeepX [] [.xmm3, .xmm1, .xmm2] s s' := by
  refine ⟨_, by
    simp (config := {decide := true}) only [Impl.Rc2.X86_64.Sse2.select,
      runBlock_cons, runStep_some, runBlock_nil, exec, XOp.exec,
      xmm_setXmm_self, xmm_setXmm_of_ne]
    rfl, ?_⟩
  refine ⟨?_, ?_, ?_⟩
  · simp (config := {decide := true}) only [selectValue, xmm_setXmm_self,
      xmm_setXmm_of_ne, XBinOp.eval]
  · exact xmm_setXmm_self _ _ _
  · constructor
    · constructor
      · intro r _; simp only [gpr_setXmm]
      · simp only [mem_setXmm]
      · simp only [rd_setXmm]
      · simp only [wr_setXmm]
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp only [xmm_setXmm_of_ne _ _ hr.1, xmm_setXmm_of_ne _ _ hr.2.1,
        xmm_setXmm_of_ne _ _ hr.2.2]

theorem selectValue_word (a b v : BitVec 128) (x y : Byte) (i : Nat) (hi : i < 8)
    (ha : word a i = x.setWidth 16) (hb : word b i = y.setWidth 16) :
    word (selectValue a b Impl.Rc2.X86_64.Sse2.ones v) i =
      if x = y then word v i else 0 := by
  rw [selectValue, word_pand, word_psraw _ _ hi, word_psubw _ _ hi]
  rw [show (15 : BitVec 8).toNat = 15 by decide, Nat.min_eq_left (by decide)]
  rw [show word (a ^^^ b) i = word a i ^^^ word b i from word_pxor a b]
  rw [Impl.Rc2.X86_64.Sse2.ones, word_ofWords _ hi, ha, hb, mask_eq]
  by_cases h : x = y
  · rw [ite_eq_left h, ite_eq_left h, BitVec.allOnes_and]
  · rw [ite_eq_right h, ite_eq_right h]
    change 0#16 &&& word v i = 0#16
    exact BitVec.zero_and

end VG.Proof.Rc2.X86_64.Sse2
