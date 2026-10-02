import VerifiedGarbage.Proof.MlDsa.AArch64.Round.Basic

/-!
# ML-DSA on AArch64: the values the rounding code computes

`Decompose` by a multiplication and shifts (`fX`, `r1X`), as 64-bit values,
and the conditional steps on the sign bit, as natural numbers, from the
target-independent lemmas of `Proof/MlDsa/Round/Decompose.lean`.
-/

namespace VG.Proof.MlDsa.AArch64.Round

open VG VG.AArch64 VG.Impl.MlDsa.AArch64.Round VG.Proof.MlDsa.Round
open VG.Spec.MlDsa (q gamma2s)

/-- `γ₂` is one of its two values. -/
abbrev IsG (g : Nat) : Prop := g = g32 ∨ g = g88

theorem isG_of_mem {g : Nat} (h : g ∈ gamma2s) : IsG g := by
  rcases mem_gamma2s h with e | e
  · exact .inr e
  · exact .inl e

theorem mem_of_isG {g : Nat} (h : IsG g) : g ∈ gamma2s := by
  rcases h with rfl | rfl <;> decide

theorem dShift_lt {g : Nat} : dShift g < 64 := by unfold dShift; split <;> decide

theorem dMod_lt {g : Nat} : dMod g < 4096 := by unfold dMod; split <;> decide

theorem dMod_eq {g : Nat} (h : IsG g) : dMod g = hbM g := by rcases h with rfl | rfl <;> rfl

theorem hbM_pos {g : Nat} (h : IsG g) : 0 < hbM g := by rcases h with rfl | rfl <;> decide

/-- `f`, as `hbRaw` computes it from `a`, with `M` and `2^(S-1)` in their registers. -/
def fX (g : Nat) (a : BitVec 64) : BitVec 64 :=
  (((a + BitVec.ofNat 64 127) >>> 7) * BitVec.ofNat 64 (hbMul g) + BitVec.ofNat 64 (hbAdd g)) >>> dShift g

/-- `r₁ = f mod m`, as `hb` computes it: `f` times the sign bit of `f - m`. -/
def r1X (g : Nat) (a : BitVec 64) : BitVec 64 := fX g a * ((fX g a - BitVec.ofNat 64 (dMod g)) >>> 63)

theorem fX_toNat {g : Nat} (hg : IsG g) {a : BitVec 64} (ha : a.toNat < q) :
    (fX g a).toNat = hbF g a.toNat := by
  have hq : q = 8380417 := rfl
  rw [hbF_eq (mem_of_isG hg) ha]
  have hM : hbMul g < 65536 := by rcases hg with rfl | rfl <;> decide
  have hA : hbAdd g ≤ 2 ^ 23 := by rcases hg with rfl | rfl <;> decide
  have hS : dShift g = hbShift g := rfl
  have e1 : ((a + BitVec.ofNat 64 127) >>> 7).toNat = (a.toNat + 127) / 128 := by
    rw [BitVec.toNat_ushiftRight, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
    congr 1; omega
  have e2 : (((a + BitVec.ofNat 64 127) >>> 7) * BitVec.ofNat 64 (hbMul g)).toNat =
      (a.toNat + 127) / 128 * hbMul g := by
    rw [BitVec.toNat_mul, e1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := hbMul g) (by omega)]
    exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.mul_le_mul (Nat.le_refl _) (Nat.le_of_lt hM))
      (by omega))
  have e3 : (((a + BitVec.ofNat 64 127) >>> 7) * BitVec.ofNat 64 (hbMul g) + BitVec.ofNat 64 (hbAdd g)).toNat =
      (a.toNat + 127) / 128 * hbMul g + hbAdd g := by
    have : (a.toNat + 127) / 128 * hbMul g < 2 ^ 40 :=
      Nat.lt_of_le_of_lt (Nat.mul_le_mul (Nat.le_refl _) (Nat.le_of_lt hM)) (by omega)
    rw [BitVec.toNat_add, e2, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := hbAdd g) (by omega)]
    omega
  rw [fX, BitVec.toNat_ushiftRight, e3, Nat.shiftRight_eq_div_pow, hS]

theorem r1X_toNat {g : Nat} (hg : IsG g) {a : BitVec 64} (ha : a.toNat < q) :
    (r1X g a).toNat = hbF g a.toNat % hbM g := by
  have hf := fX_toNat hg ha
  have hle := hbF_le (mem_of_isG hg) ha
  have hm := hbM_pos hg
  have hmv : (BitVec.ofNat 64 (dMod g)).toNat = hbM g := by
    rw [BitVec.toNat_ofNat, dMod_eq hg]; exact Nat.mod_eq_of_lt (by rcases hg with rfl | rfl <;> decide)
  have hm44 : hbM g ≤ 44 := by rcases hg with rfl | rfl <;> decide
  generalize hF : hbF g a.toNat = F at hf hle
  have hs : ((fX g a - BitVec.ofNat 64 (dMod g)) >>> 63).toNat = if F < hbM g then 1 else 0 := by
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_sub, hf, hmv]
    split <;> omega
  rw [r1X, BitVec.toNat_mul, hs, hf]
  split
  · rw [Nat.mul_one, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  · rw [Nat.mul_zero, show F = hbM g by omega, Nat.mod_self]

theorem r1X_lt {g : Nat} (hg : IsG g) {a : BitVec 64} (ha : a.toNat < q) : (r1X g a).toNat < hbM g := by
  rw [r1X_toNat hg ha]; exact Nat.mod_lt _ (hbM_pos hg)

end VG.Proof.MlDsa.AArch64.Round
