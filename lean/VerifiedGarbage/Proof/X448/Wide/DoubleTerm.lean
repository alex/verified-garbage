import VerifiedGarbage.Proof.X448.Wide.Term

/-! Untrusted: one doubled cross product in symmetric X448 squaring. -/
namespace VG.Proof.X448.Wide

open VG VG.AArch64 VG.Proof.Ed25519.Word64
open VG.Proof.Ed25519.AArch64 (mulHi read_x)
open VG.Proof.X448.AArch64 (Keeps)
open VG.Impl.X448.AArch64.Wide

theorem termFromDouble_ok (s : State) (a b : Reg) (hb : b ≠ .x10) (hb11 : b ≠ .x11)
    (ha : (s.gpr a).toNat < 2 ^ 63)
    (h : 2 * ((s.gpr a).toNat * (s.gpr b).toNat) + pair (s.gpr .x4) (s.gpr .x5) < 2 ^ 128) :
    WP isa (.block (termFromDouble a b)) s fun t =>
      pair (t.gpr .x4) (t.gpr .x5) =
        2 * ((s.gpr a).toNat * (s.gpr b).toNat) + pair (s.gpr .x4) (s.gpr .x5) ∧
      t.mem = s.mem ∧ Keeps [.x4, .x5, .x10, .x11] s t := by
  apply WP.of_runBlock
  simp only [termFromDouble, runBlock_cons, runStep_some, runBlock_nil, exec, read_x,
    RegUpd.gpr_write, RegUpd.gpr_addWithCarry, RegUpd.c_addWithCarry,
    BitVec.setWidth_eq, ite_true, ite_false, reduceCtorEq, hb, hb11,
    Option.some.injEq, exists_eq_left']
  refine ⟨?_, rfl, (fun r hr => ?_), rfl, rfl⟩
  · have doubled : (s.gpr a + s.gpr a).toNat = 2 * (s.gpr a).toNat := by
      rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by omega)]
      omega
    have cap : (s.gpr a + s.gpr a).toNat * (s.gpr b).toNat +
        pair (s.gpr .x4) (s.gpr .x5) < 2 ^ 128 := by
      rw [doubled, Nat.mul_assoc]; exact h
    have hv := madd128 (s.gpr a + s.gpr a) (s.gpr b) (s.gpr .x4) (s.gpr .x5) cap
    rw [doubled, Nat.mul_assoc] at hv
    dsimp only [addCarry, carryOut, mulHi, Size.bits] at hv ⊢
    exact hv
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, RegUpd.gpr_addWithCarry, hr, ite_false]

end VG.Proof.X448.Wide
