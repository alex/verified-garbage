import VerifiedGarbage.Proof.Poly1305.AArch64.Radix64.Setup

namespace VG.Proof.Poly1305.AArch64.Radix64
open VG VG.AArch64 VG.Impl.Poly1305.AArch64.Radix64
open VG.Proof.Poly1305.AArch64 VG.Proof.Poly1305.Limbs64 VG.PowLit

theorem add_adc_mod (a b c d : BitVec 64) :
    (a + b).toNat + 2 ^ 64 *
      (c + d + (BitVec.ofBool (decide (2 ^ 64 ≤ a.toNat + b.toNat))).setWidth 64).toNat =
      (a.toNat + b.toNat + 2 ^ 64 * (c.toNat + d.toNat)) % 2 ^ 128 := by
  have h1 := addc0 a b
  have h2 := addc1 c d (decide (2 ^ 64 ≤ a.toNat + b.toNat))
  have lo := (a + b).isLt
  have hi := (c + d + (BitVec.ofBool (decide (2 ^ 64 ≤ a.toNat + b.toNat))).setWidth 64).isLt
  omega_using [h1, h2, lo, hi]

set_option simprocs false in
theorem addS_ok (s : State) (hw : sR (s.gpr .x0) ∈ s.wr) :
    WP isa (.block addS) s fun s' =>
      (s'.gpr .x4).toNat + 2 ^ 64 * (s'.gpr .x5).toNat =
        ((s.gpr .x4).toNat + 2 ^ 64 * (s.gpr .x5).toNat +
          (s.mem.readW (off (s.gpr .x0) 40) 64).toNat +
          2 ^ 64 * (s.mem.readW (off (s.gpr .x0) 48) 64).toNat) % 2 ^ 128 ∧
      Keeps [.x4, .x5, .x13, .x14] s s' := by
  have i : ∀ d, d + 8 ≤ 128 →
      InRegions (s.rd ++ s.wr) (s.gpr .x0 + BitVec.ofNat 64 d) 8 :=
    fun d hd => ⟨_, List.mem_append_right _ hw, contains_off hd (by omega_using [hd])⟩
  have i40 := i 40 (by decide); have i48 := i 48 (by decide)
  apply WP.of_runBlock
  simp (config := {decide := true}) only [addS, runBlock_cons, runBlock_nil, isa, runStep_some,
    exec, addr, Size.bytes, State.load, i40, i48, State.read, Size.bits,
    BitVec.setWidth_eq, RegUpd.gpr_write, RegUpd.mem_write, RegUpd.rd_write, RegUpd.wr_write,
    RegUpd.gpr_addWithCarry, RegUpd.c_addWithCarry,
    ite_true, ite_false, Bool.toNat_false, Nat.add_zero, BitVec.add_zero,
    Option.map_some, Option.bind_some, Option.some.injEq, exists_eq_left', ofNat_bool]
  refine ⟨?_, fun r hr => ?_, rfl, rfl, rfl⟩
  · rw [add_adc_mod]
    congr 1
    change (s.gpr .x4).toNat + (s.mem.readW (off (s.gpr .x0) 40) 64).toNat +
      2 ^ 64 * ((s.gpr .x5).toNat + (s.mem.readW (off (s.gpr .x0) 48) 64).toNat) =
      (s.gpr .x4).toNat + 2 ^ 64 * (s.gpr .x5).toNat +
      (s.mem.readW (off (s.gpr .x0) 40) 64).toNat +
      2 ^ 64 * (s.mem.readW (off (s.gpr .x0) 48) 64).toNat
    omega_using []
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, RegUpd.gpr_addWithCarry, hr.1, hr.2.1, hr.2.2.1,
      hr.2.2.2, ite_false]

end VG.Proof.Poly1305.AArch64.Radix64
