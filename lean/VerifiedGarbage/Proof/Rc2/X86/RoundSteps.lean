import VerifiedGarbage.Impl.Rc2.X86.Block
import VerifiedGarbage.Proof.Rc2.X86.KeyLookup
import VerifiedGarbage.Proof.Rc2.X86.KeyIO
import VerifiedGarbage.Proof.Rc2.Word32

namespace VG.Proof.Rc2.X86

open VG VG.X86 VG.X86.RegUpd VG.Impl.Rc2.X86

theorem wordReg_separate (i : Nat) :
    wordReg i ≠ .esi ∧ wordReg i ≠ .edi ∧ wordReg i ≠ .ebp ∧ wordReg i ≠ .esp := by
  have fact : ∀ j < 4, wordReg j ≠ .esi ∧ wordReg j ≠ .edi ∧ wordReg j ≠ .ebp ∧ wordReg j ≠ .esp := by decide
  simpa only [wordReg, Nat.mod_mod] using fact (i % 4) (Nat.mod_lt _ (by decide))

theorem wordReg_injective : ∀ i < 4, ∀ j < 4, wordReg i = wordReg j ↔ i = j := by decide

theorem selectWord (a b c : BitVec 32) :
    ((b ^^^ c) &&& a) ^^^ c = (a &&& b) + (~~~a &&& c) := by
  rw [BitVec.add_eq_or_of_and_eq_zero]
  · apply BitVec.eq_of_getLsbD_eq
    intro j hj
    simp only [BitVec.getLsbD_xor, BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_not, hj, decide_true, Bool.true_and]
    cases a.getLsbD j <;> cases b.getLsbD j <;> cases c.getLsbD j <;> rfl
  · apply BitVec.eq_of_getLsbD_eq
    intro j hj
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_not, hj, decide_true, Bool.true_and, BitVec.getLsbD_zero]
    cases a.getLsbD j <;> cases b.getLsbD j <;> cases c.getLsbD j <;> rfl

theorem rotation_bounds (i : Nat) : 1 ≤ Spec.Rc2.rotation i ∧ Spec.Rc2.rotation i < 16 := by
  have h : ∀ j < 4, 1 ≤ Spec.Rc2.rotation j ∧ Spec.Rc2.rotation j < 16 := by decide
  simpa only [Spec.Rc2.rotation, Nat.mod_mod] using h (i % 4) (Nat.mod_lt _ (by decide))

theorem rotate16_ok (s : State) (r : Reg) (hr : r ≠ .esi)
    (x : BitVec 16) (hx : s.gpr r = x.setWidth 32)
    (n : Nat) (hn : 1 ≤ n) (hn' : n < 16) :
    ∃ s', runBlock isa (rotate16 r n) s = some s' ∧
      s'.gpr r = (x.rotateLeft n).setWidth 32 ∧ Keep [r, .esi] s s' := by
  have hleft : 1 ≤ 32 - n ∧ 32 - n ≤ 31 := by omega
  have hright : 1 ≤ 16 - n ∧ 16 - n ≤ 31 := by omega
  refine ⟨_, by
    simp only [hleft, hright, and_self, rotate16, rr, runBlock_cons, runStep_some, runBlock_nil,
      exec, execAlu, execShift, readSrc, Option.bind_some, Option.map_some,
      gpr_setReg, gpr_arithFlags, gpr_setFlags, hr, Ne.symm hr, ite_true, ite_false]
    rfl, ?_⟩
  constructor
  · simp only [gpr_setReg, gpr_arithFlags, gpr_setFlags, ite_true,
      hr, ite_false]
    rw [hx]
    exact Word32.rotateWord x n hn hn'
  · constructor
    · intro r' hr'
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr'
      simp only [gpr_setReg, gpr_arithFlags, gpr_setFlags, hr'.1, hr'.2, ite_false]
    · simp only [mem_setReg, mem_arithFlags, mem_setFlags]
    · simp only [rd_setReg, rd_arithFlags, rd_setFlags]
    · simp only [wr_setReg, wr_arithFlags, wr_setFlags]

theorem mixSelect_ok (s : State) (i : Nat) :
    ∃ s', runBlock isa (mixSelect i) s = some s' ∧
      s'.gpr .esi = (s.gpr (wordReg (i + 3)) &&& s.gpr (wordReg (i + 2))) +
        (~~~(s.gpr (wordReg (i + 3))) &&& s.gpr (wordReg (i + 1))) ∧ Keep [.esi] s s' := by
  have h1 := (wordReg_separate (i + 1)).1
  have h3 := (wordReg_separate (i + 3)).1
  refine ⟨_, by
    simp only [mixSelect, rr, runBlock_cons, runStep_some, runBlock_nil,
      exec, execAlu, readSrc, Option.bind_some, Option.map_some, gpr_setReg,
      gpr_arithFlags, h1, h3, ite_false, ite_true]
    rfl, ?_⟩
  constructor
  · rw [gpr_setReg_self]; exact selectWord _ _ _
  · constructor
    · intro r hr
      have hn : r ≠ .esi := by simpa only [List.mem_singleton] using hr
      simp only [gpr_setReg, gpr_arithFlags, hn, ite_false]
    · rfl
    · rfl
    · rfl

theorem mixKey_ok (s : State) (j : Nat) (hj : j < 64)
    (stackRead : InRegions (s.rd ++ s.wr) (argAddr s 0) 4)
    (fit : (arg s 0).toNat + 128 ≤ 2 ^ 32)
    (readable : ∀ i < 128, InRegions (s.rd ++ s.wr) (addr32 (arg s 0) + BitVec.ofNat 64 i) 1) :
    ∃ s', runBlock isa (mixKey j) s = some s' ∧
      s'.gpr .esi = ((Spec.Rc2.scheduleAt s.mem (addr32 (arg s 0))).getD j 0).setWidth 32 ∧
      Keep [.esi, .edi] s s' := by
  have lo := readable (2 * j) (by omega)
  have hi := readable (2 * j + 1) (by omega)
  have loAddr := addr_add (by omega : (arg s 0).toNat + 2 * j < 2 ^ 32)
  have hiAddr := addr_add (by omega : (arg s 0).toNat + (2 * j + 1) < 2 ^ 32)
  simp only [arg, argAddr, Nat.mul_zero, Nat.add_zero, ← addr_eq_def] at stackRead lo hi loAddr hiAddr ⊢
  refine ⟨_, by
    simp (config := {decide := true}) only [mixKey, memOp, State.ea, runBlock_cons,
      runStep_some, runBlock_nil, exec, execAlu, execShift, readSrc, State.load32, State.load8,
      gpr_setReg, gpr_setFlags, mem_setReg,
      rd_setReg, wr_setReg,
      stackRead, Option.map_some, Option.bind_some, ite_true, ite_false,
      ← addr_eq_def, loAddr, hiAddr, lo, hi]
    rfl, ?_⟩
  constructor
  · rw [gpr_setReg_self, Word32.joinBytes, scheduleAt_getD _ _ _ hj]
  · constructor
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp only [gpr_setReg, gpr_arithFlags, gpr_setFlags, hr.1, hr.2, ite_false]
    · rfl
    · rfl
    · rfl

theorem adjust_ok (sub : Bool) (s : State) (r : Reg) :
    ∃ s', runBlock isa (adjust sub r) s = some s' ∧
      s'.gpr r = (if sub then s.gpr r - s.gpr .esi else s.gpr r + s.gpr .esi) ∧
      Keep [r] s s' := by
  cases sub <;>
    refine ⟨_, by simp only [adjust, Bool.false_eq_true, ite_false, ite_true,
      runBlock_cons, exec, execAlu, readSrc, Option.bind_some, runStep_some, runBlock_nil]; rfl, ?_⟩
  all_goals
    constructor
    · exact gpr_setReg_self _ _ _
    · constructor
      · intro r' hr
        have hn : r' ≠ r := by simpa only [List.mem_singleton] using hr
        simp only [gpr_setReg, gpr_arithFlags, hn, ite_false]
      · rfl
      · rfl
      · rfl

end VG.Proof.Rc2.X86
