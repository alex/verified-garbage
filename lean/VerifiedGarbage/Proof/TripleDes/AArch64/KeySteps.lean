import VerifiedGarbage.Impl.TripleDes.AArch64.ExpandKey
import VerifiedGarbage.Proof.TripleDes.AArch64.Word
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd

namespace VG.Proof.TripleDes.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.TripleDes.AArch64

theorem rotate28_ok (s : State) (r : Reg) (hr : r ≠ .x4)
    (x : BitVec 28) (hx : s.gpr r = x.setWidth 64)
    (n : Nat) (hn : 1 ≤ n) (hn' : n < 28) :
    ∃ s', runBlock isa (Key.rotate28 r n) s = some s' ∧
      s'.gpr r = (x.rotateLeft n).setWidth 64 ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
      (∀ r', r' ≠ r → r' ≠ .x4 → s'.gpr r' = s.gpr r') := by
  have hleft : 64 - n < 64 := by omega
  have hright : 28 - n < 64 := by omega
  refine ⟨_, by
    simp only [Key.rotate28, mask, List.cons_append, List.nil_append,
      runBlock_cons, runStep_some, runBlock_nil, exec, Size.bits, hleft, hright,
      show (36 : Nat) < 64 from by decide, ite_true, State.read,
      BitVec.setWidth_eq, hr, Ne.symm hr, gpr_write, ite_false]
    rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [gpr_write, ite_true, BitVec.setWidth_eq, hr, ite_false]
    rw [hx, mask_word _ 28 (by decide) (by decide)]
    exact (VG.Proof.TripleDes.mask28 _).symm.trans (VG.Proof.TripleDes.rotate28_word x n hn hn')
  · simp only [mem_write]
  · simp only [rd_write]
  · simp only [wr_write]
  · simp only [sp_write]
  · intro r' h1 h2; simp only [gpr_write, h1, h2, ite_false]

end VG.Proof.TripleDes.AArch64
