import VerifiedGarbage.Proof.Bignum.X86_64.Loop
import VerifiedGarbage.Proof.Poly1305.Limbs64

/-!
# Multiword arithmetic on x86-64: multiply-accumulate steps

A step of `mulAddRow` (and of `reduceRow`): with a word `x` of the
accumulator at `aA`, a word `y` of the operand at `aB`, the multiplier
`rcx` and the carry `rbp`, it stores the low word of `rcx y + rbp + x` at
`aA'` (`aA` itself, or the word below) and leaves its high word in `rbp`
(`macStep_ok`).
-/

namespace VG.Proof.Bignum.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Proof.MlKem.X86_64
open VG.Proof.Poly1305.Limbs64 (add_adc_toNat)

theorem sx0 : BitVec.signExtend 64 (0 : BitVec 32) = 0 := rfl

/-- `lo + 2⁶⁴ hi = lo + c` with the carry into `hi`. -/
theorem addc_toNat (lo hi c : BitVec 64) (h : lo.toNat + c.toNat + 2 ^ 64 * hi.toNat < 2 ^ 128) :
    (lo + c).toNat + 2 ^ 64 * (hi + 0 +
      (BitVec.ofBool (decide (2 ^ 64 ≤ lo.toNat + c.toNat))).setWidth 64).toNat =
      lo.toNat + c.toNat + 2 ^ 64 * hi.toNat := by
  have := add_adc_toNat lo c hi 0 (by rw [show (0 : BitVec 64).toNat = 0 from rfl]; omega)
  rwa [show (0 : BitVec 64).toNat = 0 from rfl, Nat.add_zero] at this

/-- The product `rdx:rax` of `mul`, as a number. -/
theorem mul_toNat (a b : BitVec 64) :
    (BitVec.ofNat 64 (a.toNat * b.toNat)).toNat +
      2 ^ 64 * (BitVec.ofNat 64 (a.toNat * b.toNat / 2 ^ 64)).toNat = a.toNat * b.toNat := by
  have ha := a.isLt; have hb := b.isLt
  have hp : a.toNat * b.toNat ≤ (2 ^ 64 - 1) * (2 ^ 64 - 1) := Nat.mul_le_mul (by omega) (by omega)
  rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := a.toNat * b.toNat / 2 ^ 64) (by omega)]
  exact Nat.mod_add_div _ _

theorem mul_le (a b : BitVec 64) : a.toNat * b.toNat ≤ (2 ^ 64 - 1) * (2 ^ 64 - 1) :=
  Nat.mul_le_mul (by have := a.isLt; omega) (by have := b.isLt; omega)

/-- A multiply-accumulate step (`mac src d`) whose operand word is at `aS`,
accumulator word at `aX`, and destination at `aD`. -/
theorem mac_ok (s : State) {src : Reg} {d : Int} {aS aX aD : Addr}
    (eS : s.gpr src + s.gpr .r14 * BitVec.ofNat 64 8 + BitVec.ofInt 64 0 = aS)
    (eX : s.gpr .r8 + s.gpr .r14 * BitVec.ofNat 64 8 + BitVec.ofInt 64 0 = aX)
    (eD : s.gpr .r8 + s.gpr .r14 * BitVec.ofNat 64 8 + BitVec.ofInt 64 d = aD)
    (hS : InRegions (s.rd ++ s.wr) aS 8) (hX : InRegions (s.rd ++ s.wr) aX 8)
    (hD : InRegions s.wr aD 8) :
    WP isa (.block (mac src d)) s fun t =>
      ∃ lo : BitVec 64, t.mem = s.mem.writeW aD lo ∧
        lo.toNat + 2 ^ 64 * (t.gpr .rbp).toNat = (s.gpr .rcx).toNat * (s.mem.readW aS 64).toNat +
          (s.gpr .rbp).toNat + (s.mem.readW aX 64).toNat := by
  unfold mac
  xrun [State.ea, ix, eS, eX, eD, hS, hX, hD, sx0]
  refine ⟨_, rfl, ?_⟩
  have hm := mul_toNat (s.mem.readW aS 64) (s.gpr .rcx)
  have hl := mul_le (s.mem.readW aS 64) (s.gpr .rcx)
  have hc := (s.gpr .rbp).isLt
  have hx := (s.mem.readW aX 64).isLt
  have e1 := addc_toNat (BitVec.ofNat 64 ((s.mem.readW aS 64).toNat * (s.gpr .rcx).toNat))
    (BitVec.ofNat 64 ((s.mem.readW aS 64).toNat * (s.gpr .rcx).toNat / 2 ^ 64)) (s.gpr .rbp) (by omega)
  have e2 := addc_toNat (BitVec.ofNat 64 ((s.mem.readW aS 64).toNat * (s.gpr .rcx).toNat) + s.gpr .rbp)
    (BitVec.ofNat 64 ((s.mem.readW aS 64).toNat * (s.gpr .rcx).toNat / 2 ^ 64) + 0 +
      (BitVec.ofBool (decide (2 ^ 64 ≤ (BitVec.ofNat 64 ((s.mem.readW aS 64).toNat *
        (s.gpr .rcx).toNat)).toNat + (s.gpr .rbp).toNat))).setWidth 64) (s.mem.readW aX 64) (by omega)
  rw [e2, Nat.mul_comm (s.gpr .rcx).toNat]
  omega

end VG.Proof.Bignum.X86_64
