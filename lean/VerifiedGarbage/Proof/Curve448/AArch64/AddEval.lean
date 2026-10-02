import VerifiedGarbage.Proof.Curve448.AArch64.Stage

/-! Untrusted: pointwise coefficient in registers, without an intermediate store. -/
namespace VG.Proof.Curve448.AArch64
open VG VG.AArch64 VG.Proof.X448.Wide VG.Proof.X448.Wide.Representation
open VG.Impl.X448.AArch64 (ld st)
open VG.Proof.X448.AArch64
open VG.Impl.Curve448.AArch64

theorem addEval_ok {s : State} {base : Addr} (hs : Scr s base) {a b i : Nat}
    (ha : Slot a) (ha8 : a % 8 = 0) (hb : Slot b) (hb8 : b % 8 = 0) (hi : i < 8)
    (ab : limbs s.mem base a i < weakBound) (bb : limbs s.mem base b i < weakBound) :
    WP isa (.block (Impl.Curve448.AArch64.addEval a b i)) s fun t =>
      pair (t.gpr .x4) (t.gpr .x5) = limbs s.mem base a i + limbs s.mem base b i ∧ t.mem = s.mem ∧ Keeps [.x4, .x5] s t := by
  have la := hs.read (d := a + 8 * i) (n := 8) (by change a + 128 ≤ 3584 at ha; omega)
  have lb := hs.read (d := b + 8 * i) (n := 8) (by change b + 128 ≤ 3584 at hb; omega)
  have ae : (a + 8 * i) % 8 = 0 ∧ a + 8 * i < 32768 := by
    change a + 128 ≤ 3584 at ha; omega
  have be : (b + 8 * i) % 8 = 0 ∧ b + 8 * i < 32768 := by
    change b + 128 ≤ 3584 at hb; omega
  apply WP.of_runBlock
  simp only [Impl.Curve448.AArch64.addEval, ld, runBlock_cons, runStep_some, runBlock_nil, exec, addr, Size.bytes, Size.bits, Nat.reduceMul, Nat.reduceLT, BitVec.shiftLeft_zero,
    State.read, State.load, RegUpd.gpr_write, RegUpd.mem_write,
    RegUpd.rd_write, RegUpd.wr_write, BitVec.setWidth_eq, ae, be, and_self,
    hs.x3, la, lb, ite_true, ite_false, reduceCtorEq,
    Option.map_some, Option.bind_some, read8_eq, Option.some.injEq, exists_eq_left']
  refine ⟨?_, trivial, (fun r hr => ?_), rfl, rfl⟩
  · simp only [pair, show (BitVec.setWidth 64 (0 : BitVec 16)).toNat = 0 from rfl,
      Nat.mul_zero, Nat.add_zero, BitVec.toNat_add]
    change (limbs s.mem base a i + limbs s.mem base b i) % 2 ^ 64 = _
    exact Nat.mod_eq_of_lt (by simp only [weakBound, radix] at ab bb; omega)
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, hr.1, hr.2, ite_false]

end VG.Proof.Curve448.AArch64
