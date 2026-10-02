import VerifiedGarbage.Proof.Ed25519.AArch64.PointTableLoad

/-! Public point-table addresses are a base plus a bounded entry offset. -/
namespace VG.Proof.Ed25519.AArch64
open VG VG.AArch64 VG.Impl.Ed25519.AArch64

theorem tableAddr_ok {s : State} {base : Addr} (hp : s.gpr .x0 = base)
    (o j : Nat) (hj : j < 64) (hc : s.gpr .x19 = BitVec.ofNat 64 j) :
    WP isa (.block (tableAddr o)) s fun t =>
      t.gpr .x8 = off base (o + 128 * j) ∧ Keeps [.x8, .x3] s t := by
  have hshift : (BitVec.ofNat 64 j) <<< 7 = BitVec.ofNat 64 (128 * j) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
      Nat.shiftLeft_eq, BitVec.toNat_ofNat]
    rw [show 2 ^ 7 = 128 from rfl, Nat.mul_comm]
    rw [Nat.mod_eq_of_lt (by omega : j < 2 ^ 64), Nat.mod_eq_of_lt (by omega : 128 * j < 2 ^ 64)]
  apply WP.of_runBlock
  simp only [tableAddr, const64, List.cons_append, List.nil_append,
    runBlock_cons, runStep_some, runBlock_nil, exec, read_x,
    show (7 : Nat) < Size.x.bits from by decide,
    show 16 * 0 < Size.x.bits from by decide, show 16 * 1 < Size.x.bits from by decide,
    show 16 * 2 < Size.x.bits from by decide, show 16 * 3 < Size.x.bits from by decide,
    RegUpd.gpr_write, BitVec.setWidth_eq, hc, hp, hshift,
    ite_true, ite_false, reduceCtorEq, movz_movk64', Option.some.injEq, exists_eq_left']
  refine ⟨?_, ⟨fun r hr => ?_, rfl, rfl, rfl, rfl⟩⟩
  · rw [BitVec.add_comm (BitVec.ofNat 64 (128 * j)), BitVec.add_assoc, ← BitVec.ofNat_add,
      Nat.add_comm (128 * j)]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, hr.1, hr.2, ite_false]

end VG.Proof.Ed25519.AArch64
