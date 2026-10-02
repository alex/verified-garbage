import VerifiedGarbage.Proof.X448.AArch64.Small

/-! Untrusted: a24 coefficient in registers, without an intermediate store. -/
namespace VG.Proof.X448.AArch64
open VG VG.AArch64 VG.Impl.X448.AArch64

theorem smallEval_ok {s : State} {base : Addr} (hs : Scr s base) {a i : Nat}
    (ha : Slot a) (ha8 : a % 8 = 0) (hi : i < 16) :
    WP isa (.block (Pointwise.smallEval a i)) s fun t =>
      t.gpr .x4 = BitVec.ofNat 64 (39081 * limbs s.mem base a i) ∧
      t.mem = s.mem ∧ Keeps [.x4, .x5] s t := by
  have la := hs.read (d := a + 8 * i) (n := 8) (by change a + 128 ≤ 3584 at ha; omega)
  have ae : (a + 8 * i) % 8 = 0 ∧ a + 8 * i < 32768 := by
    change a + 128 ≤ 3584 at ha; omega
  apply WP.of_runBlock
  simp only [Pointwise.smallEval, ld, runBlock_cons, runStep_some, runBlock_nil, exec,
    addr, Size.bytes, Size.bits, Nat.reduceMul, Nat.reduceLT, BitVec.shiftLeft_zero,
    State.read, State.load, RegUpd.gpr_write, RegUpd.mem_write,
    BitVec.setWidth_eq, ae, and_self, hs.x3, la, ite_true, ite_false, reduceCtorEq,
    Option.map_some, Option.bind_some, read8_eq, Option.some.injEq, exists_eq_left']
  refine ⟨?_, trivial, (fun r hr => ?_), rfl, rfl⟩
  · apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_mul, show (BitVec.setWidth 64 (39081 : BitVec 16)).toNat = 39081 by decide,
      Nat.mul_comm _ 39081, BitVec.toNat_ofNat]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, hr.1, hr.2, ite_false]

end VG.Proof.X448.AArch64
