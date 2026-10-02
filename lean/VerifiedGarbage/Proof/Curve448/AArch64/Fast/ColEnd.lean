import VerifiedGarbage.Proof.Curve448.AArch64.Fast.MOp

/-!
# The end of a column: carry in, stage a limb, carry out

Untrusted: everything here is checked by Lean.
-/

namespace VG.Proof.Curve448.AArch64.Fast

open VG VG.AArch64 VG.Proof.Ed25519.Word64
open VG.Impl.Curve448.AArch64.Fast
open VG.Impl.X448.AArch64 (ld st)
open VG.Proof.X448.Wide (pair low56 add128 radix)
open VG.Proof.X448.AArch64 (Keeps Scr word off load_sc addr_word read8_eq write8_eq)
open VG.Proof.Ed25519.AArch64 (read_x)

theorem extr56 (lo hi : BitVec 64) :
    ((hi ++ lo).extractLsb' 56 64).toNat = pair lo hi / 2 ^ 56 % 2 ^ 64 := by
  rw [BitVec.extractLsb'_toNat, BitVec.toNat_append, ← Nat.shiftLeft_add_eq_or_of_lt lo.isLt,
    Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]
  simp only [pair]
  congr 2
  omega

theorem mask_val : (BitVec.ofNat 64 (2 ^ 56 - 1) : BitVec 64) =
    (0x00ff : BitVec 16).setWidth 64 <<< 48 ||| ((0xffff : BitVec 16).setWidth 64 <<< 32 |||
      ((0xffff : BitVec 16).setWidth 64 <<< 16 ||| (0xffff : BitVec 16).setWidth 64)) := by
  decide

/-- Add the carry `c`: `ZERO` holds zero. -/
theorem carryIn_ok (s : State) (a : Acc) (c : Reg) (h₁ : a.lo ≠ a.hi) (h₂ : a.lo ≠ ZERO)
    (hz : s.gpr ZERO = 0) (hlt : accVal s a + (s.gpr c).toNat < 2 ^ 128) :
    WP isa (.block [.adds .x a.lo a.lo c, .adcs .x a.hi a.hi ZERO]) s fun t =>
      accVal t a = accVal s a + (s.gpr c).toNat ∧ t.mem = s.mem ∧ Keeps [a.lo, a.hi] s t := by
  refine WP.of_runBlock ⟨_, by simp only [runBlock_cons, runStep_some, runBlock_nil, exec]; rfl, ?_⟩
  refine ⟨?_, rfl, fun q hq => ?_, rfl, rfl⟩
  · have := add128 (s.gpr a.lo) (s.gpr a.hi) (s.gpr c) hlt
    simp only [accVal, read_x, RegUpd.gpr_addWithCarry, RegUpd.c_addWithCarry, h₁, Ne.symm h₁,
      Ne.symm h₂, ite_true, ite_false, BitVec.setWidth_eq, hz]
    dsimp only [addCarry, carryOut, Size.bits] at this ⊢
    exact this
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hq
    simp only [read_x, RegUpd.gpr_addWithCarry, hq.1, hq.2, ite_false]

/-- Stage the low 56 bits of `a` at `STAGE + 8k` and carry the rest into `c`. -/
theorem stage_ok {s : State} {base : Addr} (hs : Scr s base) (t : Reg) (a : Acc) (c : Reg)
    {k : Nat} (hk : k < 8) (h₁ : t ≠ a.lo) (h₂ : t ≠ a.hi) (h₄ : t ≠ .x3)
    (hm : s.gpr MASK = BitVec.ofNat 64 (2 ^ 56 - 1)) (hlt : accVal s a < 2 ^ 120) :
    WP isa (.block [.logic .and .x t a.lo MASK, st t (STAGE + 8 * k), .extr .x c a.hi a.lo 56]) s
      fun u => u.mem = s.mem.writeW (off base (STAGE + 8 * k))
          (BitVec.ofNat 64 (accVal s a % radix)) ∧
        (u.gpr c).toNat = accVal s a / radix ∧ Keeps [t, c] s u := by
  have w := hs.write (d := STAGE + 8 * k) (n := 8) (by simp only [STAGE, VG.Impl.X448.AArch64.TMP]; omega)
  have oe : (STAGE + 8 * k) % 8 = 0 ∧ STAGE + 8 * k < 32768 := by
    simp only [STAGE, VG.Impl.X448.AArch64.TMP]; omega
  have hv : (s.gpr a.lo &&& s.gpr MASK) = BitVec.ofNat 64 (accVal s a % radix) := by
    apply BitVec.eq_of_toNat_eq
    rw [hm, low56 (s.gpr a.lo) (s.gpr a.hi), BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (Nat.lt_trans (Nat.mod_lt _ (by decide)) (by decide))]
    rfl
  refine WP.of_runBlock ⟨_, by
    simp only [st, runBlock_cons, runStep_some, runBlock_nil, exec, addr, Size.bytes, Size.bits,
      read_x, State.store, RegUpd.gpr_write, RegUpd.wr_write, oe, and_self, Ne.symm h₄,
      ite_false, hs.x3, w, ite_true, Option.bind_some, show 56 < 64 from by decide]; rfl, ?_⟩
  refine ⟨?_, ?_, fun q hq => ?_, rfl, rfl⟩
  · simp only [RegUpd.mem_write, BitVec.setWidth_eq, write8_eq, hv]
  · simp only [RegUpd.gpr_write, ite_true, Ne.symm h₁, Ne.symm h₂, ite_false]
    rw [BitVec.setWidth_eq, extr56, Nat.mod_eq_of_lt (by
      have := hlt; unfold accVal at this; omega)]
    rfl
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hq
    simp only [RegUpd.gpr_write, hq.1, hq.2, ite_false]

end VG.Proof.Curve448.AArch64.Fast
