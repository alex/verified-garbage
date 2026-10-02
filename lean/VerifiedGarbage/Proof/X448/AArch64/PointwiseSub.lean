import VerifiedGarbage.Proof.X448.AArch64.AddSub

/-! Untrusted: pointwise coefficient in registers, without an intermediate store. -/
namespace VG.Proof.X448.AArch64
open VG VG.AArch64 VG.Impl.X448.AArch64

theorem subEval_ok {s : State} {base : Addr} (hs : Scr s base) {a b i : Nat}
    (ha : Slot a) (ha8 : a % 8 = 0) (hb : Slot b) (hb8 : b % 8 = 0) (hi : i < 16)
    (ab : limbs s.mem base a i < radix) (bb : limbs s.mem base b i < radix) :
    WP isa (.block (Pointwise.subEval a b i)) s fun t =>
      t.gpr .x4 = BitVec.ofNat 64 (difference (limbs s.mem base a) (limbs s.mem base b) i) ∧ t.mem = s.mem ∧ Keeps [.x4, .x5] s t := by
  have la := hs.read (d := a + 8 * i) (n := 8) (by change a + 128 ≤ 3584 at ha; omega)
  have lb := hs.read (d := b + 8 * i) (n := 8) (by change b + 128 ≤ 3584 at hb; omega)
  have biasb := bias_bound i
  have ae : (a + 8 * i) % 8 = 0 ∧ a + 8 * i < 32768 := by
    change a + 128 ≤ 3584 at ha; omega
  have be : (b + 8 * i) % 8 = 0 ∧ b + 8 * i < 32768 := by
    change b + 128 ≤ 3584 at hb; omega
  apply WP.of_runBlock
  simp only [Pointwise.subEval, ld, runBlock_cons, runStep_some, runBlock_nil, exec, addr, Size.bytes,
    Size.bits, Nat.reduceLT, Nat.reduceMul, BitVec.shiftLeft_zero, State.read, State.load, RegUpd.gpr_write, RegUpd.mem_write,
    RegUpd.rd_write, RegUpd.wr_write, BitVec.setWidth_eq, ae, be, and_self,
    hs.x3, la, lb, ite_true, ite_false, reduceCtorEq,
    Option.map_some, Option.bind_some, read8_eq, Option.some.injEq, exists_eq_left']
  refine ⟨?_, trivial, (fun r hr => ?_), rfl, rfl⟩
  · apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_sub, BitVec.toNat_add, subK_nat, BitVec.toNat_ofNat, difference]
    change (2 ^ 64 - limbs s.mem base b i + (limbs s.mem base a i + bias i) % 2 ^ 64) % 2 ^ 64 =
      (limbs s.mem base a i + bias i - limbs s.mem base b i) % 2 ^ 64
    have hr : radix = 268435456 := rfl
    omega
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, hr.1, hr.2, ite_false]

end VG.Proof.X448.AArch64
