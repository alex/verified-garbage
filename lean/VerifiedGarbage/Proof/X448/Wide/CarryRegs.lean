import VerifiedGarbage.Proof.X448.Wide.Reduce

/-! Untrusted: extracting a radix-2⁵⁶ digit and one-word carry. -/
namespace VG.Proof.X448.Wide

open VG VG.AArch64
open VG.Impl.X448.AArch64.Wide VG.Proof.X448.AArch64 VG.Proof.Ed25519.Word64
open VG.Proof.Ed25519.AArch64 (read_x)

theorem carryRegs_ok (s : State) (hz : s.gpr .x11 = 0)
    (hm : s.gpr .x9 = BitVec.ofNat 64 (2 ^ 56 - 1))
    (hb : pair (s.gpr .x4) (s.gpr .x5) + (s.gpr .x6).toNat < 2 ^ 119) :
    let v := pair (s.gpr .x4) (s.gpr .x5) + (s.gpr .x6).toNat
    WP isa (.block carryRegs) s fun t =>
      (t.gpr .x4).toNat = v % radix ∧ (t.gpr .x6).toNat = v / radix ∧
      t.mem = s.mem ∧ Keeps [.x4, .x5, .x6] s t := by
  intro v
  let lo := addCarry (s.gpr .x4) (s.gpr .x6) false
  let hi := addCarry (s.gpr .x5) 0 (carryOut (s.gpr .x4) (s.gpr .x6) false)
  have hv : pair lo hi = v := add128 _ _ _ (Nat.lt_trans hb (by decide))
  have hd := low56 lo hi
  have hc := high56 lo hi (by rw [hv]; exact hb)
  rw [hv] at hd hc
  apply WP.of_runBlock
  simp only [carryRegs, runBlock_cons, runStep_some, runBlock_nil, exec, read_x,
    RegUpd.gpr_write, RegUpd.gpr_addWithCarry, RegUpd.c_addWithCarry,
    BitVec.setWidth_eq, ite_true, ite_false, reduceCtorEq, hz, hm,
    show 56 < Size.x.bits from by decide, show 8 < Size.x.bits from by decide,
    Option.some.injEq, exists_eq_left']
  refine ⟨?_, ?_, rfl, (fun r hr => ?_), rfl, rfl⟩
  · dsimp only [lo, hi, addCarry, carryOut, Size.bits] at hd ⊢
    exact hd
  · dsimp only [lo, hi, addCarry, carryOut, Size.bits] at hc ⊢
    exact hc
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, RegUpd.gpr_addWithCarry, hr, ite_false]

end VG.Proof.X448.Wide
