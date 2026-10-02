import VerifiedGarbage.Proof.Gcm.X86.Pclmul.Groups

namespace VG.Proof.Gcm.X86.Pclmul
open VG.X86 VG.X86.RegUpd VG.Proof.Gcm.Poly

/-- Append a low dword to the lower ninety-six bits of the previous value. -/
def catWord (v : BitVec 128) (d : BitVec 32) : BitVec 128 :=
  (v <<< 32) ||| ((0 : BitVec 96) ++ d)

def assembled (c : BitVec 128) : BitVec 128 :=
  catWord (catWord (catWord ((0 : BitVec 96) ++ c.extractLsb' 96 32)
    (c.extractLsb' 64 32)) (c.extractLsb' 32 32)) (c.extractLsb' 0 32)

theorem assembled_eq (c : BitVec 128) : assembled c = c := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [assembled, catWord, BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft,
    BitVec.getLsbD_append, BitVec.getLsbD_extractLsb']
  rcases (by omega : i < 32 ∨ (32 ≤ i ∧ i < 64) ∨ (64 ≤ i ∧ i < 96) ∨ 96 ≤ i)
    with h | h | h | h <;>
    simp (disch := omega) only [ite_eq_left, ite_eq_right, decide_eq_true,
      decide_eq_false, Bool.true_and, Bool.false_and, Bool.not_true, Bool.not_false,
      Bool.false_or, BitVec.ofNat_eq_ofNat, BitVec.getLsbD_zero, Bool.or_false] <;>
    exact congrArg _ (by omega)

/-- Setup changes only eax and the listed vector registers. -/
structure SetupFrame (rs : List XReg) (s s' : State) : Prop where
  gpr : ∀ r, r ≠ .eax → s'.gpr r = s.gpr r
  mem : s'.mem = s.mem
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  xmm : ∀ r, r ∉ rs → s'.xmm r = s.xmm r

theorem const_ok (r : XReg) (c : BitVec 128) (s : State) (hr : r ≠ .xmm5) :
    WP isa (.block (Impl.Gcm.X86.Pclmul.const r c)) s fun s' =>
      s'.xmm r = c ∧ SetupFrame [r, .xmm5] s s' := by
  apply WP.of_runBlock
  simp only [Impl.Gcm.X86.Pclmul.const, List.range_succ, List.range_zero,
    List.flatMap_cons, List.flatMap_nil, List.append_nil,
    List.cons_append, List.nil_append]
  simp (config := {decide := true}) only [runBlock_cons, runStep_some, runBlock_nil,
    exec, isa, readSrc, XOp.exec, gpr_setReg, xmm_setReg, xmm_setXmm,
    ite_true, ite_false, hr, Ne.symm hr, Option.map_some, Option.some.injEq,
    exists_eq_left', XShiftOp.eval, XBinOp.eval]
  refine ⟨?_, fun a ha => ?_, ?_, ?_, ?_, fun a ha => ?_⟩
  · exact assembled_eq c
  · simp only [gpr_setXmm, gpr_setReg, ha, ite_false]
  · simp only [mem_setXmm, mem_setReg]
  · simp only [rd_setXmm, rd_setReg]
  · simp only [wr_setXmm, wr_setReg]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at ha
    simp only [xmm_setXmm, xmm_setReg, ha.1, ha.2, ite_false]

theorem unpack_ones : XBinOp.eval .punpckldq
    ((0 : BitVec 96) ++ (0xffffffff : BitVec 32))
    ((0 : BitVec 96) ++ (0xffffffff : BitVec 32)) =
    ((0 : BitVec 64) ++ (0xffffffffffffffff : BitVec 64)) := rfl

theorem hInv_ok (s : State) :
    WP isa (.block Impl.Gcm.X86.Pclmul.hInv) s fun s' =>
      x * φ (s'.xmm .xmm3) = φ (s.xmm .xmm7) ∧
      SetupFrame [.xmm3, .xmm4, .xmm5, .xmm6] s s' := by
  rw [Impl.Gcm.X86.Pclmul.hInv, WP.block_append_iff]
  refine WP.mono (const_ok .xmm4 Impl.Gcm.X86.Pclmul.xInv s (by decide))
    fun s₁ ⟨hc, hf⟩ => ?_
  have h7 : s₁.xmm .xmm7 = s.xmm .xmm7 := hf.xmm _ (by decide)
  apply WP.of_runBlock
  simp (config := {decide := true}) only [runBlock_cons, runStep_some, runBlock_nil,
    exec, isa, readSrc, XOp.exec, gpr_setReg, xmm_setReg, xmm_setXmm,
    ite_true, ite_false, Option.map_some, Option.some.injEq, exists_eq_left',
    hc, h7, eval_movdqa, eval_pxor, unpack_ones]
  refine ⟨?_, fun a ha => ?_, ?_, ?_, ?_, fun a ha => ?_⟩
  · change x * φ ((XShiftOp.eval .psllq (s.xmm .xmm7) 1 |||
      XShiftOp.eval .pslldq (XShiftOp.eval .psrlq (s.xmm .xmm7) 63) 8) ^^^ _) = _
    rw [shl1, mask_eq, x_φ_hInv]
  · simp only [gpr_setXmm, gpr_setReg, ha, ite_false]
    exact hf.gpr a ha
  · simp only [mem_setXmm, mem_setReg]; exact hf.mem
  · simp only [rd_setXmm, rd_setReg]; exact hf.rd
  · simp only [wr_setXmm, wr_setReg]; exact hf.wr
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at ha
    simp only [xmm_setXmm, xmm_setReg, ha.1, ha.2.2.1, ha.2.2.2, ite_false]
    exact hf.xmm a (by simp only [List.mem_cons, List.not_mem_nil,
      ha.2.1, ha.2.2.1, or_self, not_false_eq_true])

end VG.Proof.Gcm.X86.Pclmul
