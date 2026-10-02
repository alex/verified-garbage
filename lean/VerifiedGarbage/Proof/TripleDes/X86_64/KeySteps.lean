import VerifiedGarbage.Impl.TripleDes.X86_64.ExpandKey
import VerifiedGarbage.Proof.TripleDes.Word
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd

namespace VG.Proof.TripleDes.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.TripleDes.X86_64

theorem rotate28_ok (s : State) (r : Reg) (hr : r ≠ .rax)
    (x : BitVec 28) (hx : s.gpr r = x.setWidth 64)
    (n : Nat) (hn : 1 ≤ n) (hn' : n < 28) :
    ∃ s', runBlock isa (Key.rotate28 r n) s = some s' ∧
      s'.gpr r = (x.rotateLeft n).setWidth 64 ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r', r' ≠ r → r' ≠ .rax → s'.gpr r' = s.gpr r') := by
  have hleft : 1 ≤ 64 - n ∧ 64 - n ≤ 63 := by omega
  have hright : 1 ≤ 28 - n ∧ 28 - n ≤ 63 := by omega
  refine ⟨_, by
    simp only [Key.rotate28, rr, runBlock_cons, runStep_some, runBlock_nil, exec,
      execAlu, execShift, readSrc, hleft, hright, and_self, ite_true, hr, Ne.symm hr,
      Option.bind_some, Option.map_some, gpr_setReg, gpr_setFlags, gpr_arithFlags,
      ite_false]
    rfl, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [gpr_setReg, gpr_arithFlags, gpr_setFlags, ite_true, hr, ite_false]
    rw [hx]
    exact VG.Proof.TripleDes.rotate28_word x n hn hn'
  · simp only [mem_setReg, mem_arithFlags, mem_setFlags]
  · simp only [rd_setReg, rd_arithFlags, rd_setFlags]
  · simp only [wr_setReg, wr_arithFlags, wr_setFlags]
  · intro r' h1 h2
    simp only [gpr_setReg, gpr_arithFlags, gpr_setFlags, h1, h2, ite_false]

end VG.Proof.TripleDes.X86_64
