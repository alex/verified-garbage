import VerifiedGarbage.Proof.MlDsa.Pack.Hint
import VerifiedGarbage.Proof.MlDsa.Pack.Coeffs

/-!
# ML-DSA: hints in memory, for every target

Untrusted: everything here is checked by Lean. The parameters `(ω, k)` of
the hint encodings, the coefficients of a hint stored as words (`hintAt`),
and facts the proofs of `HintBitPack` and `HintBitUnpack` share on every
target.
-/

namespace VG.Proof.MlDsa.Pack

open VG.Spec.MlDsa

theorem mem_hintParams {ω k : Nat} (h : (ω, k) ∈ hintParams) : 4 ≤ k ∧ k ≤ 8 ∧ ω ≤ 80 := by
  simp only [hintParams, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at h
  omega

/-- Coefficient `j` of polynomial `i` of the hint at `p`. -/
theorem hintAt_get {m : Mem} {p : Addr} {k i j : Nat} (hi : i < k) (hj : j < n) :
    ((hintAt m p k).getD i noHint)[j]! = decide (coeffAt m p (256 * i + j) ≠ 0) := by
  rw [hintAt, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi, Option.map_some,
    Option.getD_some, getElem!_pos _ j hj, Vector.getElem_ofFn]

theorem hintAt_length (m : Mem) (p : Addr) (k : Nat) : (hintAt m p k).length = k := by simp [hintAt]

theorem coeffAt_zeroMem (p : Addr) (i : Nat) : coeffAt (fun _ => 0#8) p i = 0#32 := by
  simp only [coeffAt, Mem.readW, Mem.read]
  rfl

theorem filter_false : ((Vector.ofFn fun _ : Fin n => false).toList.filter id) = [] := by
  rw [List.filter_eq_nil_iff]; intro a ha; simp at ha; simp [ha]

theorem sum_zero : ∀ l : List Nat, (l.map fun _ => 0).sum = 0
  | [] => rfl
  | _ :: l => by rw [List.map_cons, List.sum_cons, sum_zero l]

/-- The hint in memory of zeros has no 1s. -/
theorem hintOnes_zero (p : Addr) (k : Nat) : hintOnes (hintAt (fun _ => 0) p k) = 0 := by
  simp [hintOnes, hintAt, coeffAt_zeroMem, Function.comp_def, filter_false, sum_zero]

theorem map_toNat_inj : ∀ {b₁ b₂ : List Byte}, b₁.map (·.toNat) = b₂.map (·.toNat) → b₁ = b₂
  | [], [], _ => rfl
  | _ :: _, _ :: _, h => by
    simp only [List.map_cons, List.cons.injEq] at h
    rw [BitVec.eq_of_toNat_eq h.1, map_toNat_inj h.2]
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h

/-- A byte of the words of a region of zero words. -/
theorem byte_of_zero_words {m : Mem} {p : Addr} {N : Nat} (hz : ∀ t < N, coeffAt m p t = 0) {a : Addr}
    (ha : (⟨p, N * 4⟩ : Region).Contains a 1) : m a = 0 := by
  simp only [Region.Contains] at ha
  have ht : (a - p).toNat % 4 < 4 := Nat.mod_lt _ (by decide)
  have ea : a = coeffAddr p ((a - p).toNat / 4) + BitVec.ofNat 64 ((a - p).toNat % 4) := by
    rw [coeffAddr, BitVec.add_assoc, BitVec.ofNat_add_ofNat, Nat.div_add_mod, BitVec.ofNat_toNat,
      BitVec.setWidth_eq, BitVec.add_comm, BitVec.sub_add_cancel]
  rw [ea, Mem.readW_byte m (coeffAddr p _) ht, ← coeffAt_eq, hz _ (by omega)]
  simp

/-- `a - b` in 64 bits, for `a, b < 2⁶³`: its sign bit says whether `a < b`. -/
theorem sub_lsr63 {a b : BitVec 64} (ha : a.toNat < 2 ^ 63) (hb : b.toNat < 2 ^ 63) :
    ((a - b) >>> 63).toNat = if a.toNat < b.toNat then 1 else 0 := by
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_sub]
  split <;> omega

end VG.Proof.MlDsa.Pack
