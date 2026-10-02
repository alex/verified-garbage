import VerifiedGarbage.Impl.TripleDes.Arm.ExpandKey
import VerifiedGarbage.Proof.TripleDes.Arm.Word
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Arm.RegUpd

namespace VG.Proof.TripleDes.Arm
open VG VG.Arm VG.Arm.RegUpd VG.Impl.TripleDes.Arm

theorem rotate28_ok (s : State) (r : Reg) (hr : r ≠ .r4)
    (x : BitVec 28) (hx : s.gpr r = x.setWidth 32)
    (n : Nat) (hn : 1 ≤ n) (hn' : n < 5) :
    ∃ s', runBlock isa (Key.rotate28 r n) s = some s' ∧
      s'.gpr r = (x.rotateLeft n).setWidth 32 ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
      (∀ r', r' ≠ r → r' ≠ .r4 → s'.gpr r' = s.gpr r') := by
  have hleft : 1 ≤ 32 - n ∧ 32 - n ≤ 31 := by omega
  have hright : 1 ≤ 28 - n ∧ 28 - n ≤ 31 := by omega
  refine ⟨_, by
    simp only [Key.rotate28, mask, List.cons_append, List.nil_append,
      runBlock_cons, runStep_some, runBlock_nil, exec, Op2.eval, hleft.1, hleft.2, hright.1, hright.2,
      show 1 ≤ (4 : Nat) from by decide, show (4 : Nat) ≤ 31 from by decide, and_self, ite_true, Option.map_some,
      hr, Ne.symm hr, gpr_setReg, ite_false]
    rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [gpr_setReg, ite_true, hr, ite_false]
    rw [hx, mask_word _ 28 (by decide) (by decide)]
    exact (mask28 _).symm.trans (rotate28_word x n hn hn')
  · simp only [mem_setReg]
  · simp only [rd_setReg]
  · simp only [wr_setReg]
  · simp only [sp_setReg]
  · intro r' h1 h2; simp only [gpr_setReg, h1, h2, ite_false]
end VG.Proof.TripleDes.Arm
