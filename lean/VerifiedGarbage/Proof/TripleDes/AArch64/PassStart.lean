import VerifiedGarbage.Proof.TripleDes.AArch64.Loop
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd

namespace VG.Proof.TripleDes.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.TripleDes.AArch64
open VG.Spec.TripleDes (Direction)

def passOffset (component : Nat) (direction : Direction) : Nat :=
  128 * component + if direction = .encrypt then 0 else 120

theorem passOffset_bound : ∀ c < 3, ∀ d : Direction, passOffset c d < 4096 := by
  intro c hc d
  cases d <;> simp only [passOffset, reduceCtorEq, ite_true, ite_false] <;> omega

theorem passStart_ok (component : Nat) (hc : component < 3) (direction : Direction)
    (s : State) :
    ∃ s', runBlock isa (passStart component direction) s = some s' ∧
      s'.gpr .x22 = s.gpr .x0 + BitVec.ofNat 64 (passOffset component direction) ∧
      s'.gpr .x21 = BitVec.ofNat 64 16 ∧ s'.mem = s.mem ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
      (∀ r, r ≠ .x21 → r ≠ .x22 → s'.gpr r = s.gpr r) := by
  have hb := passOffset_bound component hc direction
  change 128 * component + (if direction = .encrypt then 0 else 120) < 4096 at hb
  refine ⟨_, by
    simp only [passStart, imm, runBlock_cons, runStep_some, runBlock_nil, exec,
      hb, ite_true, Size.bits, Nat.mul_zero,
      show (0 : Nat) < 64 from by decide, State.read, BitVec.setWidth_eq]
    rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [gpr_write, reduceCtorEq, ite_false, ite_true, BitVec.setWidth_eq]
    rfl
  · simp only [gpr_write, ite_true, BitVec.setWidth_eq]; rfl
  · simp only [mem_write]
  · simp only [rd_write]
  · simp only [wr_write]
  · simp only [sp_write]
  · intro r hr₁ hr₂
    simp only [gpr_write, hr₁, hr₂, ite_false]

end VG.Proof.TripleDes.AArch64
