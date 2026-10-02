import VerifiedGarbage.Impl.MlDsa.X86_64.Round.Round
import VerifiedGarbage.Proof.MlDsa.Round.Decompose

/-!
# ML-DSA on x86-64: what the rounding code computes

The values the code of `Impl/MlDsa/X86_64/Round/Round.lean` leaves in its
registers, as the symbolic execution of a block writes them (`condAddV`,
`hbRawV`, `hbV`), and what they are as natural numbers (`condAddV_toNat`,
`hbRawV_toNat`, `hbV_toNat`), from the target-independent lemmas of
`Proof/MlDsa/Round/Decompose.lean`.
-/

namespace VG.Proof.MlDsa.X86_64.Round

open VG VG.X86_64 VG.Impl.MlDsa.X86_64.Round
open VG.Spec.MlDsa (q gamma2s)
open VG.Proof.MlDsa.Round (hbF q_eq mem_gamma2s hbF_le hbF_eq)

/-- A 32-bit immediate below `2³¹`, sign-extended. -/
theorem sx_toNat {k : BitVec 32} (h : k.toNat < 2 ^ 31) : (BitVec.signExtend 64 k).toNat = k.toNat := by
  have : k.msb = false := by rw [BitVec.msb_eq_decide]; simp only [decide_eq_false_iff_not]; omega
  rw [BitVec.toNat_signExtend, this, BitVec.toNat_setWidth]
  simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
  omega

theorem sx_ofNat_toNat {k : Nat} (h : k < 2 ^ 31) : (BitVec.signExtend 64 (BitVec.ofNat 32 k)).toNat = k := by
  rw [sx_toNat (by rw [BitVec.toNat_ofNat]; omega), BitVec.toNat_ofNat]; omega

theorem setWidth64_toNat (x : BitVec 32) : (BitVec.setWidth 64 x).toNat = x.toNat := by
  rw [BitVec.toNat_setWidth]; have := x.isLt; omega

/-! ## Conditional addition -/

/-- What `condAdd r x m k` leaves in `r`: `r - x`, plus `k` if it borrows. -/
def condAddV (r x : BitVec 64) (k : BitVec 32) : BitVec 64 :=
  r - x + (0#64 - BitVec.setWidth 64 (BitVec.ofBool (decide (r.toNat < x.toNat))) &&& BitVec.signExtend 64 k)

theorem condAddV_toNat {r x : BitVec 64} {k : BitVec 32} (hk : k.toNat < 2 ^ 31) (hx : x.toNat ≤ r.toNat + k.toNat) :
    (condAddV r x k).toNat = if r.toNat < x.toNat then r.toNat + k.toNat - x.toNat else r.toNat - x.toNat := by
  have hs := sx_toNat hk
  have hr := r.isLt
  have hx' := x.isLt
  unfold condAddV
  by_cases h : r.toNat < x.toNat
  · rw [decide_eq_true h, ite_eq_left_of_eq_true _ _ (eq_true h)]
    have e : (0#64 - BitVec.setWidth 64 (BitVec.ofBool true)) = BitVec.allOnes 64 := by decide
    rw [e, BitVec.allOnes_and, BitVec.toNat_add, BitVec.toNat_sub, hs]
    omega
  · rw [decide_eq_false h, ite_eq_right_of_eq_false _ _ (eq_false h)]
    have e : (0#64 - BitVec.setWidth 64 (BitVec.ofBool false)) = 0#64 := by decide
    rw [e, BitVec.zero_and, BitVec.add_zero, BitVec.toNat_sub]
    omega

/-- `condAdd` of an immediate `k` and mask `k`: the conditional subtraction of `k`. -/
theorem condAddV_imm_toNat {r : BitVec 64} {k : Nat} (hk : k < 2 ^ 31) (hr : r.toNat < 2 * k) :
    (condAddV r (BitVec.signExtend 64 (BitVec.ofNat 32 k)) (BitVec.ofNat 32 k)).toNat = r.toNat % k := by
  have e := sx_ofNat_toNat hk
  have e' : (BitVec.ofNat 32 k).toNat = k := by rw [BitVec.toNat_ofNat]; omega
  rw [condAddV_toNat (by omega) (by omega), e, e']
  split
  · rw [Nat.mod_eq_of_lt (by omega)]; omega
  · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]

/-! ## `Decompose` -/

/-- What `hbRaw g` leaves in `rax` from `a`. -/
def hbRawV (g : Nat) (a : BitVec 64) : BitVec 64 :=
  (BitVec.ofNat 64 (((a + BitVec.signExtend 64 (127 : BitVec 32)) >>> 7).toNat *
      (BitVec.setWidth 64 (BitVec.ofNat 32 (dMul g))).toNat) +
    BitVec.signExtend 64 (BitVec.ofNat 32 (dAdd g))) >>> dShift g

theorem dMul_eq (g : Nat) : dMul g = Proof.MlDsa.Round.hbMul g := rfl
theorem dAdd_eq (g : Nat) : dAdd g = Proof.MlDsa.Round.hbAdd g := rfl
theorem dShift_eq (g : Nat) : dShift g = Proof.MlDsa.Round.hbShift g := rfl

theorem dMod_eq {g : Nat} (h : g ∈ gamma2s) : dMod g = Proof.MlDsa.Round.hbM g := by
  rcases mem_gamma2s h with rfl | rfl <;> rfl

theorem hbRawV_toNat {g : Nat} (h : g ∈ gamma2s) {a : BitVec 64} (ha : a.toNat < q) :
    (hbRawV g a).toNat = hbF g a.toNat := by
  rw [q_eq] at ha
  have hM : dMul g ≤ 11275 := by unfold dMul; split <;> decide
  have hA : dAdd g ≤ 2 ^ 23 := by unfold dAdd; split <;> decide
  have e1 : (a + BitVec.signExtend 64 (127 : BitVec 32)).toNat = a.toNat + 127 := by
    rw [BitVec.toNat_add, show (BitVec.signExtend 64 (127 : BitVec 32)).toNat = 127 by decide]; omega
  have e2 : ((a + BitVec.signExtend 64 (127 : BitVec 32)) >>> 7).toNat = (a.toNat + 127) / 128 := by
    rw [BitVec.toNat_ushiftRight, e1, Nat.shiftRight_eq_div_pow]
  have e3 : (BitVec.setWidth 64 (BitVec.ofNat 32 (dMul g))).toNat = dMul g := by
    rw [setWidth64_toNat, BitVec.toNat_ofNat]; omega
  have hp : (a.toNat + 127) / 128 * dMul g ≤ 65473 * 11275 :=
    Nat.mul_le_mul (by omega) hM
  have e4 : (BitVec.ofNat 64 (((a + BitVec.signExtend 64 (127 : BitVec 32)) >>> 7).toNat *
      (BitVec.setWidth 64 (BitVec.ofNat 32 (dMul g))).toNat) +
      BitVec.signExtend 64 (BitVec.ofNat 32 (dAdd g))).toNat = (a.toNat + 127) / 128 * dMul g + dAdd g := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, e2, e3, sx_ofNat_toNat (by omega)]
    omega
  unfold hbRawV
  rw [BitVec.toNat_ushiftRight (BitVec.ofNat 64 _ + _), e4, Nat.shiftRight_eq_div_pow, hbF_eq h (by rw [q_eq]; exact ha)]
  rfl

/-- What `hb g` leaves in `rax` from `a`. -/
def hbV (g : Nat) (a : BitVec 64) : BitVec 64 :=
  condAddV (hbRawV g a) (BitVec.signExtend 64 (BitVec.ofNat 32 (dMod g))) (BitVec.ofNat 32 (dMod g))

theorem hbV_toNat {g : Nat} (h : g ∈ gamma2s) {a : BitVec 64} (ha : a.toNat < q) :
    (hbV g a).toNat = hbF g a.toNat % Proof.MlDsa.Round.hbM g := by
  have hM : dMod g ≤ 44 ∧ 16 ≤ dMod g := by unfold dMod; split <;> decide
  have hf := hbF_le h ha
  rw [← dMod_eq h] at hf ⊢
  rw [hbV, condAddV_imm_toNat (by omega) (by rw [hbRawV_toNat h ha]; omega), hbRawV_toNat h ha]

end VG.Proof.MlDsa.X86_64.Round
