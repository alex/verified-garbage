import VerifiedGarbage.Proof.ChaCha20.AArch64.Mixed8.Chunk
import VerifiedGarbage.Proof.ChaCha20.AArch64.Neon4.Loop

namespace VG.Proof.ChaCha20.AArch64.Mixed8
open VG VG.AArch64 VG.Impl.ChaCha20.AArch64.Mixed8
open VG.Spec.ChaCha20 (stateAt)

/-- The high bit tests the public number of complete blocks against eight.
Dividing the byte count by 64 first makes the test valid for every u64 length. -/
theorem less8 (n : Nat) (hn : n < 2 ^ 64) :
    ((BitVec.ofNat 64 n >>> 6) - BitVec.ofNat 64 8) >>> 63 =
      BitVec.ofNat 64 (if n < 512 then 1 else 0) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ushiftRight, BitVec.toNat_sub, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt hn, Nat.shiftRight_eq_div_pow]
  have hd : n / 2 ^ 6 < 2 ^ 58 := by omega
  by_cases h : n < 512
  · rw [ite_eq_left h]
    have hb : n / 2 ^ 6 < 8 := by omega
    omega
  · rw [ite_eq_right h]
    have hb : 8 ≤ n / 2 ^ 6 := by omega
    omega

theorem check_ok (s : State) :
    WP isa (.block check) s fun u =>
      u.gpr .x5 = BitVec.ofNat 64 (if (s.gpr .x2).toNat < 512 then 1 else 0) ∧
      (∀ r, r ≠ .x5 → u.gpr r = s.gpr r) ∧
      u.mem = s.mem ∧ u.rd = s.rd ∧ u.wr = s.wr ∧ u.v = s.v ∧ u.sp = s.sp := by
  apply WP.of_runBlock
  simp (config := {decide := true}) only [check, runBlock_cons, runBlock_nil, exec,
    State.read, Size.bits, ite_true, isa, runStep_some, RegUpd.gpr_write,
    BitVec.setWidth_eq, Option.some.injEq, exists_eq_left']
  refine ⟨?_,fun r hr => by simp only [hr,ite_false],rfl,rfl,rfl,rfl,rfl⟩
  simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq] using less8 (s.gpr .x2).toNat (s.gpr .x2).isLt

end VG.Proof.ChaCha20.AArch64.Mixed8
