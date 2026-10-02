import VerifiedGarbage.Proof.Curve448.AArch64.Stage
namespace VG.Proof.Curve448.AArch64
open VG VG.AArch64 VG.Proof.X448.Wide
open VG.Impl.X448.AArch64 (ld st)
open VG.Proof.X448.AArch64
open VG.Proof.Ed25519.AArch64 (mulHi read_x mul_lo_hi)

theorem smallEval_ok {s : State} {base : Addr} (hs : Scr s base) {a i : Nat}
    (ha : Slot a) (ha8 : a % 8 = 0) (hi : i < 8) :
    WP isa (.block (Impl.Curve448.AArch64.smallEval a i)) s fun t =>
      pair (t.gpr .x4) (t.gpr .x5) = 39081 * limbs s.mem base a i ∧
      t.mem = s.mem ∧ Keeps [.x4, .x5, .x6] s t := by
  have la := hs.read (d := a + 8 * i) (n := 8) (by change a + 128 ≤ 3584 at ha; omega)
  have ae : (a + 8 * i) % 8 = 0 ∧ a + 8 * i < 32768 := by
    change a + 128 ≤ 3584 at ha; omega
  apply WP.of_runBlock
  simp only [Impl.Curve448.AArch64.smallEval, ld, runBlock_cons, runStep_some, runBlock_nil, exec,
    addr, Size.bytes, Size.bits, Nat.reduceMul, Nat.reduceLT, BitVec.shiftLeft_zero,
    State.read, State.load, RegUpd.gpr_write, RegUpd.mem_write,
    BitVec.setWidth_eq, ae, and_self, hs.x3, la, ite_true, ite_false, reduceCtorEq,
    Option.map_some, Option.bind_some, read8_eq, Option.some.injEq, exists_eq_left']
  refine ⟨?_, trivial, (fun r hr => ?_), rfl, rfl⟩
  · have h := mul_lo_hi (word s.mem base (a + 8 * i)) (BitVec.setWidth 64 (39081 : BitVec 16))
    rw [show (BitVec.setWidth 64 (39081 : BitVec 16)).toNat = 39081 by decide, Nat.mul_comm _ 39081] at h
    dsimp only [pair, mulHi, Size.bits] at h ⊢
    exact h
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, hr, ite_false]
end VG.Proof.Curve448.AArch64
