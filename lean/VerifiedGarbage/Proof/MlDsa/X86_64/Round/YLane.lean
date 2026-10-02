import VerifiedGarbage.Impl.MlDsa.X86_64.Round.Avx2
import VerifiedGarbage.Proof.MlDsa.Round.Decompose
import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.VArith

/-!
# ML-DSA on x86-64: what the AVX2 rounding code computes in a doubleword

What `hbX` and `lbX` (`Impl/MlDsa/X86_64/Round/Avx2.lean`) compute in each
doubleword (`hbL`, `lbL`), and that it is `r₁` and `r₀` of `Decompose`
(`hbL_toNat`, `lbL_toNat`): every intermediate value fits in 32 bits.
-/

namespace VG.Proof.MlDsa.X86_64.Round

open VG VG.X86_64 VG.Impl.MlDsa.X86_64.Round
open VG.Spec.MlDsa (q gamma2s ofInt lowBits)
open VG.Proof.MlDsa.Round (hbF hbM q_eq mem_gamma2s hbF_le hbF_eq hbM_mul lowBits_val)
open VG.Proof.MlDsa.X86_64.Arith (caddL caddL_toNat sshiftRight31)

/-- `t · (1 + Σ 2^k)` by shifts and additions, as `mulX` computes it. -/
def mulL (sh : List Nat) (t : BitVec 32) : BitVec 32 := sh.foldl (fun acc k => acc + (t <<< k)) t

theorem foldl_toNat (t : BitVec 32) : ∀ (sh : List Nat) (acc : BitVec 32),
    acc.toNat + t.toNat * (sh.map (2 ^ ·)).sum < 2 ^ 32 →
      (sh.foldl (fun acc k => acc + (t <<< k)) acc).toNat = acc.toNat + t.toNat * (sh.map (2 ^ ·)).sum
  | [], acc, _ => by simp
  | k :: sh, acc, h => by
    simp only [List.map_cons, List.sum_cons, Nat.mul_add] at h ⊢
    have hk : (t <<< k).toNat = t.toNat * 2 ^ k := by
      rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.mod_eq_of_lt (by omega)]
    have ha : (acc + t <<< k).toNat = acc.toNat + t.toNat * 2 ^ k := by
      rw [BitVec.toNat_add, hk, Nat.mod_eq_of_lt (by omega)]
    rw [List.foldl_cons, foldl_toNat t sh _ (by rw [ha]; omega), ha]
    omega

theorem mulL_toNat (sh : List Nat) {t : BitVec 32} (h : t.toNat * (1 + (sh.map (2 ^ ·)).sum) < 2 ^ 32) :
    (mulL sh t).toNat = t.toNat * (1 + (sh.map (2 ^ ·)).sum) := by
  rw [mulL, foldl_toNat t sh t (by rw [Nat.mul_add] at h; omega), Nat.mul_add]; omega

theorem dSh_sum {g : Nat} (h : g ∈ gamma2s) : 1 + ((dSh g).map (2 ^ ·)).sum = dMul g := by
  rcases mem_gamma2s h with rfl | rfl <;> rfl

/-- `f`, as `hbX` computes it in a doubleword. -/
def hbFL (g : Nat) (x : BitVec 32) : BitVec 32 :=
  (mulL (dSh g) ((x + BitVec.ofNat 32 127) >>> 7) + BitVec.ofNat 32 (dAdd g)) >>> dShift g

/-- What `hbX` computes in a doubleword. -/
def hbL (g : Nat) (x : BitVec 32) : BitVec 32 :=
  hbFL g x &&& (hbFL g x - BitVec.ofNat 32 (dMod g)).sshiftRight (min (31 : BitVec 8).toNat 32)

theorem dMod_eq' {g : Nat} (h : g ∈ gamma2s) : dMod g = hbM g := by
  rcases mem_gamma2s h with rfl | rfl <;> rfl

/-- `f` in 32 bits. -/
theorem hbF32 {g : Nat} (h : g ∈ gamma2s) {x : BitVec 32} (hx : x.toNat < q) :
    (hbFL g x).toNat = hbF g x.toNat := by
  rw [q_eq] at hx
  have e1 : (x + BitVec.ofNat 32 127).toNat = x.toNat + 127 := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have e2 : ((x + BitVec.ofNat 32 127) >>> 7).toNat = (x.toNat + 127) / 128 := by
    rw [BitVec.toNat_ushiftRight, e1, Nat.shiftRight_eq_div_pow]
  have hM : dMul g ≤ 11275 := by unfold dMul; split <;> decide
  have hA : dAdd g ≤ 2 ^ 23 := by unfold dAdd; split <;> decide
  have hp : (x.toNat + 127) / 128 * dMul g ≤ 65473 * 11275 := Nat.mul_le_mul (by omega) hM
  have e3 : (mulL (dSh g) ((x + BitVec.ofNat 32 127) >>> 7)).toNat = (x.toNat + 127) / 128 * dMul g := by
    rw [mulL_toNat _ (by rw [e2, dSh_sum h]; omega), e2, dSh_sum h]
  have e4 : (mulL (dSh g) ((x + BitVec.ofNat 32 127) >>> 7) + BitVec.ofNat 32 (dAdd g)).toNat =
      (x.toNat + 127) / 128 * dMul g + dAdd g := by
    rw [BitVec.toNat_add, e3, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show dAdd g < 2 ^ 32 by omega)]; omega
  rw [hbFL, BitVec.toNat_ushiftRight, e4, Nat.shiftRight_eq_div_pow, hbF_eq h (by rw [q_eq]; exact hx)]
  rfl

theorem hbL_toNat {g : Nat} (h : g ∈ gamma2s) {x : BitVec 32} (hx : x.toNat < q) :
    (hbL g x).toNat = hbF g x.toNat % hbM g := by
  have hf := hbF32 h hx
  have hle := hbF_le h hx
  have hm : dMod g ≤ 44 ∧ 16 ≤ dMod g := by unfold dMod; split <;> decide
  rw [← dMod_eq' h] at hle ⊢
  unfold hbL
  generalize hbFL g x = f at hf ⊢
  rw [sshiftRight31]
  have hsub : (f - BitVec.ofNat 32 (dMod g)).toNat = (f.toNat + 2 ^ 32 - dMod g) % 2 ^ 32 := by
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show dMod g < 2 ^ 32 by omega)]; omega
  by_cases e : hbF g x.toNat = dMod g
  · rw [ite_eq_left (by rw [hsub, hf, e]; omega), show f &&& (0 : BitVec 32) = 0 from BitVec.and_zero, e, Nat.mod_self]; rfl
  · rw [ite_eq_right (by rw [hsub, hf]; omega), show (-1 : BitVec 32) = BitVec.allOnes 32 by decide, BitVec.and_allOnes,
      hf, Nat.mod_eq_of_lt (by omega)]

/-- `r₁ · 2γ₂` by shifts and additions, as `mul2X` computes it. -/
def mul2L (g : Nat) (r : BitVec 32) : BitVec 32 :=
  if g = 261888 then r <<< 19 - r <<< 9
  else [13, 14, 15, 17].foldl (fun acc k => acc + (r <<< k)) (r <<< 11)

theorem mul2L_toNat {g : Nat} (h : g ∈ gamma2s) {r : BitVec 32} (hr : r.toNat ≤ 44) :
    (mul2L g r).toNat = r.toNat * (2 * g) := by
  have s : ∀ k ≤ 19, (r <<< k).toNat = r.toNat * 2 ^ k := fun k hk => by
    rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.mod_eq_of_lt]
    calc r.toNat * 2 ^ k ≤ 44 * 2 ^ 19 := Nat.mul_le_mul hr (Nat.pow_le_pow_right (by decide) hk)
      _ < 2 ^ 32 := by decide
  rcases mem_gamma2s h with rfl | rfl
  · unfold mul2L
    rw [ite_eq_right (by decide)]
    simp only [List.foldl_cons, List.foldl_nil]
    rw [BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_add, s 11 (by decide), s 13 (by decide),
      s 14 (by decide), s 15 (by decide), s 17 (by decide)]
    omega
  · unfold mul2L
    rw [ite_eq_left rfl, BitVec.toNat_sub, s 19 (by decide), s 9 (by decide)]
    omega

/-- What `lbX` computes in a doubleword. -/
def lbL (g : Nat) (x : BitVec 32) : BitVec 32 := caddL (x - mul2L g (hbL g x))

theorem lbL_toNat {g : Nat} (h : g ∈ gamma2s) {x : BitVec 32} (hx : x.toNat < q) :
    (lbL g x).toNat = (ofInt (lowBits g (Fin.ofNat q x.toNat))).val := by
  have hv : (Fin.ofNat q x.toNat).val = x.toNat := Nat.mod_eq_of_lt hx
  rw [lowBits_val h, hv]
  have hlt : hbF g x.toNat % hbM g < hbM g := Nat.mod_lt _ (by rcases mem_gamma2s h with rfl | rfl <;> decide)
  have hM : hbM g ≤ 44 := by rcases mem_gamma2s h with rfl | rfl <;> decide
  have hle : hbF g x.toNat % hbM g * (2 * g) ≤ q - 1 := by
    rw [← hbM_mul h]; exact Nat.mul_le_mul_right _ (Nat.le_of_lt hlt)
  have e1 : (mul2L g (hbL g x)).toNat = hbF g x.toNat % hbM g * (2 * g) := by
    rw [mul2L_toNat h (by rw [hbL_toNat h hx]; omega), hbL_toNat h hx]
  unfold lbL
  rw [caddL_toNat, BitVec.toNat_sub, e1]
  rw [q_eq] at hx hle ⊢
  split <;> split <;> omega

end VG.Proof.MlDsa.X86_64.Round
