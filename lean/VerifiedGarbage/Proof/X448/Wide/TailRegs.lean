import VerifiedGarbage.Impl.X448.AArch64.Tail
import VerifiedGarbage.Proof.X448.Wide.TailBounds
import VerifiedGarbage.Proof.X448.Wide.UnpackRegs

/-! Untrusted: a one-word carry step after wide reduction. -/
namespace VG.Proof.X448.Wide

open VG VG.AArch64 VG.Proof.X448.AArch64

theorem pair_low64 (lo hi : BitVec 64) (h : pair lo hi < 2 ^ 64) :
    hi.toNat = 0 ∧ lo.toNat = pair lo hi := by
  simp only [pair] at h ⊢
  omega

theorem tailRegs_ok (s : State) (hm : s.gpr .x9 = BitVec.ofNat 64 (2 ^ 56 - 1))
    (hb : (s.gpr .x4).toNat + (s.gpr .x6).toNat < 2 ^ 64) :
    let v := (s.gpr .x4).toNat + (s.gpr .x6).toNat
    WP isa (.block Impl.X448.AArch64.Tail.regs) s fun t =>
      (t.gpr .x4).toNat = v % radix ∧ (t.gpr .x6).toNat = v / radix ∧
      t.mem = s.mem ∧ Keeps [.x4, .x6] s t := by
  intro v
  have hv : (s.gpr .x4 + s.gpr .x6).toNat = v := by rw [BitVec.toNat_add, Nat.mod_eq_of_lt hb]
  have hd := low56 (s.gpr .x4 + s.gpr .x6) 0
  simp only [pair, show (0 : BitVec 64).toNat = 0 from rfl, Nat.mul_zero, Nat.add_zero, hv] at hd
  have hc : ((s.gpr .x4 + s.gpr .x6) >>> 56).toNat = v / radix := by
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, hv]
    rfl
  apply WP.of_runBlock
  simp only [Impl.X448.AArch64.Tail.regs, runBlock_cons, runStep_some, runBlock_nil, exec,
    State.read, Size.bits, RegUpd.gpr_write, BitVec.setWidth_eq, ite_true, ite_false,
    reduceCtorEq, Nat.reduceLT, hm, Option.some.injEq, exists_eq_left']
  refine ⟨hd, hc, rfl, (fun r hr => ?_), rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [RegUpd.gpr_write, hr, ite_false]

end VG.Proof.X448.Wide
