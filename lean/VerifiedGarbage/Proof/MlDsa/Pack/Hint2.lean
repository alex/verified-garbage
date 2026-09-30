import VerifiedGarbage.Proof.MlDsa.Pack.Hint
import VerifiedGarbage.Proof.MlDsa.Pack.Mem

/-!
# ML-DSA: `HintBitPack` and `HintBitUnpack` in memory, for every target

Untrusted: everything here is checked by Lean. What an implementation of
`HintBitPack` and `HintBitUnpack` that follows the folds of `Pack/Hint.lean`
needs about memory and the parameters, on any target: the parameters of
`hintParams`, the coefficients of `hintAt` and when two memories give the
same hint (`hintAt_congr`, from equal leaks: `coeffAt_of_leak`), the
state of the fold of `HintBitPack` after `i` polynomials and `j` more
coefficients (`hpS`, `hpT`), and the words of a hint that `HintBitUnpack`
fills in (`HArr`).
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

/-- The hint is a function of its words. -/
theorem hintAt_congr {m m' : Mem} {p : Addr} {k : Nat}
    (h : ∀ t < 256 * k, coeffAt m p t = coeffAt m' p t) : hintAt m p k = hintAt m' p k := by
  unfold hintAt
  refine List.map_congr_left fun i hi => ?_
  have hi := List.mem_range.mp hi
  refine Vector.ext fun j hj => ?_
  simp only [Vector.getElem_ofFn]
  rw [h _ (by rw [n_eq] at hj; omega)]

/-- Words whose values are the same numbers are equal. -/
theorem coeffAt_of_leak {m m' : Mem} {p : Addr} {N : Nat}
    (h : (List.range N).map (fun i => (coeffAt m p i).toNat) = (List.range N).map (fun i => (coeffAt m' p i).toNat)) :
    ∀ t < N, coeffAt m p t = coeffAt m' p t := fun t ht =>
  BitVec.eq_of_toNat_eq (List.map_inj_left.mp h t (List.mem_range.mpr ht))

/-- Lists of bytes with the same numbers are equal. -/
theorem map_toNat_inj : ∀ {b₁ b₂ : List Byte}, b₁.map (·.toNat) = b₂.map (·.toNat) → b₁ = b₂
  | [], [], _ => rfl
  | _ :: _, _ :: _, h => by
    simp only [List.map_cons, List.cons.injEq] at h
    rw [BitVec.eq_of_toNat_eq h.1, map_toNat_inj h.2]
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h

/-! ## Memory of zeros -/

theorem read_zero (a : Addr) : ∀ k, Mem.read (fun _ => 0) a k = 0
  | 0 => rfl
  | k + 1 => by
    rw [Mem.read, read_zero (a + 1) k]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_append]
    have (w : Nat) : (0 : BitVec w).toNat = 0 := BitVec.toNat_zero
    rw [this, this, this]
    rfl

theorem coeffAt_zero (p : Addr) (i : Nat) : coeffAt (fun _ => 0) p i = 0 := by
  simp only [coeffAt, Mem.readW, read_zero]
  rfl

theorem coeffAt_zero' (p : Addr) (i : Nat) : coeffAt (fun _ => 0#8) p i = 0#32 := coeffAt_zero p i

theorem filter_false : ((Vector.ofFn fun _ : Fin n => false).toList.filter id) = [] := by
  rw [List.filter_eq_nil_iff]; intro a ha; simp at ha; simp [ha]

theorem sum_zero : ∀ l : List Nat, (l.map fun _ => 0).sum = 0
  | [] => rfl
  | _ :: l => by rw [List.map_cons, List.sum_cons, sum_zero l]

/-- A hint of zero words has no 1s. -/
theorem hintOnes_of_zero {m : Mem} {p : Addr} {k : Nat} (h : ∀ t < 256 * k, coeffAt m p t = 0) :
    hintOnes (hintAt m p k) = 0 := by
  rw [hintAt_congr (m' := fun _ => 0) fun t ht => by rw [h t ht, coeffAt_zero]]
  simp [hintOnes, hintAt, coeffAt_zero', Function.comp_def, filter_false, sum_zero]

/-! ## `HintBitPack` -/

/-- The spec's state after `i` polynomials. -/
def hpS (ω k : Nat) (h : List (Vector Bool n)) (i : Nat) : Array Byte × Nat :=
  (List.range i).foldl (hpPoly ω h) (Array.replicate (ω + k) 0, 0)

/-- ... and `j` coefficients of polynomial `i`. -/
def hpT (ω k : Nat) (h : List (Vector Bool n)) (i j : Nat) : Array Byte × Nat :=
  (List.range j).foldl (hpStep (h.getD i noHint)) (hpS ω k h i)

theorem hpS_zero (ω k : Nat) (h : List (Vector Bool n)) : hpS ω k h 0 = (Array.replicate (ω + k) 0, 0) := rfl

theorem hpT_zero (ω k : Nat) (h : List (Vector Bool n)) (i : Nat) : hpT ω k h i 0 = hpS ω k h i := rfl

theorem hpS_idx (ω k : Nat) (h : List (Vector Bool n)) (i : Nat) : (hpS ω k h i).2 = onesBefore h i 0 := by
  rw [hpS, hpPolys_idx]; exact Nat.zero_add _

theorem hpT_idx (ω k : Nat) (h : List (Vector Bool n)) (i j : Nat) : (hpT ω k h i j).2 = onesBefore h i j := by
  rw [hpT, hpSteps_idx, hpS_idx]; unfold onesBefore; rfl

theorem hpT_succ (ω k : Nat) (h : List (Vector Bool n)) (i j : Nat) :
    hpT ω k h i (j + 1) = hpStep (h.getD i noHint) (hpT ω k h i j) j := by
  rw [hpT, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]; rfl

theorem hpS_succ (ω k : Nat) (h : List (Vector Bool n)) (i : Nat) :
    hpS ω k h (i + 1) = ((hpT ω k h i n).1.set! (ω + i) (BitVec.ofNat 8 (hpT ω k h i n).2), (hpT ω k h i n).2) := by
  rw [hpS, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
  rfl

theorem hintBitPack_hpS (ω k : Nat) (h : List (Vector Bool n)) : hintBitPack ω k h = (hpS ω k h k).1.toList :=
  hintBitPack_eq ω k h

/-- The index before a 1 is less than `ω`. -/
theorem hpT_idx_lt {ω k : Nat} {h : List (Vector Bool n)} (hk : h.length = k) (hω : hintOnes h ≤ ω) {i j : Nat}
    (hi : i < k) (hj : j < n) (h1 : (h.getD i noHint)[j]! = true) : (hpT ω k h i j).2 < ω := by
  rw [hpT_idx]; have := hpIdx_lt hk hi hj h1; omega

/-- The index after a polynomial is at most `ω`. -/
theorem hpT_idx_le {ω k : Nat} {h : List (Vector Bool n)} (hk : h.length = k) (hω : hintOnes h ≤ ω) {i : Nat}
    (hi : i < k) : (hpT ω k h i n).2 ≤ ω := by
  rw [hpT_idx]; have := onesBefore_n_le hk hi; omega

/-! ## `HintBitUnpack` -/

/-- The `256k` words at `p` are the hint `hA`. -/
def HArr (m : Mem) (p : Addr) (k : Nat) (hA : Array (Vector Bool n)) : Prop :=
  hA.size = k ∧ ∀ i < k, ∀ j < 256, coeffAt m p (256 * i + j) = BitVec.ofNat 32 ((hA.getD i noHint)[j]!).toNat

/-- Setting coefficient `b` of polynomial `i`. -/
theorem harr_set {m : Mem} {p : Addr} {k : Nat} (hk : k ≤ 8) {hA : Array (Vector Bool n)} (hh : HArr m p k hA)
    {i b : Nat} (hi : i < k) (hb : b < 256) :
    HArr (m.writeW (coeffAddr p (256 * i + b)) (1 : BitVec 32)) p k (huSet i b hA) := by
  refine ⟨by rw [huSet_size, hh.1], fun i' hi' j hj => ?_⟩
  rw [huSet_get (by rw [hh.1]; exact hi) (show j < n from hj)]
  by_cases e : i' = i ∧ j = b
  · obtain ⟨rfl, rfl⟩ := e
    rw [coeffAt_eq, Mem.readW_writeW_self32, ite_pos' ⟨rfl, rfl⟩]; rfl
  · rw [ite_neg' e, coeffAt_eq, Mem.readW_writeW_sep (Offset.sep _ (by
      have : 256 * i' + j ≠ 256 * i + b := fun h' => e ⟨by omega, by omega⟩
      omega) (by omega) (by omega)) (by decide), ← coeffAt_eq, hh.2 i' hi' j hj]

/-- Zero words are the hint of zeros. -/
theorem harr_zero {m : Mem} {p : Addr} {k : Nat} (hz : ∀ t < 256 * k, coeffAt m p t = 0) :
    HArr m p k (Array.replicate k noHint) := by
  refine ⟨Array.size_replicate, fun i hi j hj => ?_⟩
  rw [hz _ (by omega)]
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_replicate, hi, ite_true, Option.getD_some, noHint]
  rw [getElem!_pos _ j (show j < n from hj), Vector.getElem_replicate]
  rfl

theorem harr_congr {m m' : Mem} {p : Addr} {k : Nat} {hA : Array (Vector Bool n)} (hh : HArr m p k hA)
    (h : ∀ t < 256 * k, coeffAt m' p t = coeffAt m p t) : HArr m' p k hA :=
  ⟨hh.1, fun i hi j hj => by rw [h _ (by omega)]; exact hh.2 i hi j hj⟩

/-- The hint of the spec, from the words. -/
theorem harr_hintIs {m : Mem} {p : Addr} {k : Nat} {hA : Array (Vector Bool n)} (hh : HArr m p k hA) :
    HintIs m p k hA.toList := by
  refine ⟨by rw [Array.length_toList, hh.1], fun i hi j hj => ?_⟩
  rw [hh.2 i hi j hj]
  congr 3
  rw [List.getD_eq_getElem?_getD, Array.getElem?_toList, ← Array.getD_eq_getD_getElem?]

theorem huStep_idx {y : Array Byte} {i first : Nat} {st st' : Array (Vector Bool n) × Nat} {x : Nat}
    (h : huStep y i first st x = some st') : st'.2 = st.2 + 1 := by
  unfold huStep at h
  split at h
  · cases h
  · cases h; rfl

end VG.Proof.MlDsa.Pack
