import VerifiedGarbage.Impl.TripleDes.X86.ExpandKey
import VerifiedGarbage.Proof.TripleDes.X86.Word
import VerifiedGarbage.Proof.Rc2.X86.RoundSteps

namespace VG.Proof.TripleDes.X86.Key
open VG VG.X86 VG.X86.RegUpd VG.Impl.TripleDes.X86
open VG.Impl.TripleDes.X86.Key
open VG.Proof.Rc2.X86 (Keep)

theorem rotate28_ok (s : State) (r : Reg) (hr : r ≠ .eax)
    (x : BitVec 28) (hx : s.gpr r = x.setWidth 32)
    (n : Nat) (hn : 1 ≤ n) (hn' : n < 5) :
    ∃ s', runBlock isa (rotate28 r n) s = some s' ∧
      s'.gpr r = (x.rotateLeft n).setWidth 32 ∧ Keep [r, .eax] s s' := by
  have hleft : 1 ≤ 32 - n ∧ 32 - n ≤ 31 := by omega
  have hright : 1 ≤ 28 - n ∧ 28 - n ≤ 31 := by omega
  refine ⟨_, by
    simp only [hleft, hright, and_self, rotate28, rr, runBlock_cons, runStep_some, runBlock_nil,
      exec, execAlu, execShift, readSrc, Option.bind_some, Option.map_some,
      gpr_setReg, gpr_arithFlags, gpr_setFlags, hr, Ne.symm hr, ite_true, ite_false]
    rfl, ?_⟩
  constructor
  · simp only [gpr_setReg, gpr_arithFlags, gpr_setFlags, ite_true,
      hr, ite_false]
    rw [hx]
    exact VG.Proof.TripleDes.X86.rotate28_word x n hn hn'
  · constructor
    · intro r' hr'
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr'
      simp only [gpr_setReg, gpr_arithFlags, gpr_setFlags, hr'.1, hr'.2, ite_false]
    · simp only [mem_setReg, mem_arithFlags, mem_setFlags]
    · simp only [rd_setReg, rd_arithFlags, rd_setFlags]
    · simp only [wr_setReg, wr_arithFlags, wr_setFlags]

end VG.Proof.TripleDes.X86.Key
