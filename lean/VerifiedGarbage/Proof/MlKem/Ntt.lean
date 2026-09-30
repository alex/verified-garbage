import VerifiedGarbage.Proof.MlKem.Arith

/-!
# ML-KEM: the NTT as butterflies, for every target

Untrusted: everything here is checked by Lean. `NTT` (Algorithm 9) and
`NTT⁻¹` (Algorithm 10) restated as the loops an implementation runs, so
that its proof is only about its instructions:

* the tables `zetas` (`ζ^BitRev7(k) mod q`, FIPS 203 Appendix A) and
  `gammas` (`ζ^(2BitRev7(i)+1) mod q`, for `MultiplyNTTs`), as numbers;
* one butterfly, `bfly` (Algorithm 9, lines 8–10) or `bflyInv` (Algorithm
  10, lines 8–10), and what it does to each coefficient (`bfly_get`,
  `bflyInv_get`);
* the three nested loops: `ntt f` is `nttLayer` for each `len` of `nttLens`,
  a layer is `nttBlock` for each of its blocks, and a block is `len`
  butterflies. `nttBlockN` and `nttLayerN` are the loops after their first
  `t` iterations (`…_zero`, `…_succ`), for loop invariants, and
  `nttBlockN_get` says what each coefficient is after `t` butterflies of a
  block. Likewise `nttInvLayer`, `nttInvBlock`, `nttInvBlockN`;
* the flat list of butterflies (`ntt_eq_ops`, `nttInv_eq_ops`);
* `MultiplyNTTs` coefficient by coefficient (`multiplyNTTs_even`,
  `multiplyNTTs_odd`).

The zeta of the block `b` of the layer with `len` (`k` in the loops, `i` in
the standard) is `128 / len + b` in `NTT` (the standard's counter `i` runs
from 1 up) and `256 / len - 1 - b` in `NTT⁻¹` (from 127 down).
-/

namespace VG.Proof.MlKem

open VG.Spec.MlKem

/-! ## The tables -/

/-- `ζ^BitRev7(k) mod q` for `k < 128` (FIPS 203 Appendix A), the zetas of
the NTT. -/
def zetas : List Nat := [
  1, 1729, 2580, 3289, 2642, 630, 1897, 848, 1062, 1919, 193, 797, 2786, 3260, 569, 1746, 296,
  2447, 1339, 1476, 3046, 56, 2240, 1333, 1426, 2094, 535, 2882, 2393, 2879, 1974, 821, 289, 331,
  3253, 1756, 1197, 2304, 2277, 2055, 650, 1977, 2513, 632, 2865, 33, 1320, 1915, 2319, 1435,
  807, 452, 1438, 2868, 1534, 2402, 2647, 2617, 1481, 648, 2474, 3110, 1227, 910, 17, 2761, 583,
  2649, 1637, 723, 2288, 1100, 1409, 2662, 3281, 233, 756, 2156, 3015, 3050, 1703, 1651, 2789,
  1789, 1847, 952, 1461, 2687, 939, 2308, 2437, 2388, 733, 2337, 268, 641, 1584, 2298, 2037,
  3220, 375, 2549, 2090, 1645, 1063, 319, 2773, 757, 2099, 561, 2466, 2594, 2804, 1092, 403,
  1026, 1143, 2150, 2775, 886, 1722, 1212, 1874, 1029, 2110, 2935, 885, 2154]

/-- `ζ^(2BitRev7(i) + 1) mod q` for `i < 128` (FIPS 203 Appendix A), the
moduli `γ` of `MultiplyNTTs`. -/
def gammas : List Nat := [
  17, 3312, 2761, 568, 583, 2746, 2649, 680, 1637, 1692, 723, 2606, 2288, 1041, 1100, 2229, 1409,
  1920, 2662, 667, 3281, 48, 233, 3096, 756, 2573, 2156, 1173, 3015, 314, 3050, 279, 1703, 1626,
  1651, 1678, 2789, 540, 1789, 1540, 1847, 1482, 952, 2377, 1461, 1868, 2687, 642, 939, 2390,
  2308, 1021, 2437, 892, 2388, 941, 733, 2596, 2337, 992, 268, 3061, 641, 2688, 1584, 1745, 2298,
  1031, 2037, 1292, 3220, 109, 375, 2954, 2549, 780, 2090, 1239, 1645, 1684, 1063, 2266, 319,
  3010, 2773, 556, 757, 2572, 2099, 1230, 561, 2768, 2466, 863, 2594, 735, 2804, 525, 1092, 2237,
  403, 2926, 1026, 2303, 1143, 2186, 2150, 1179, 2775, 554, 886, 2443, 1722, 1607, 1212, 2117,
  1874, 1455, 1029, 2300, 2110, 1219, 2935, 394, 885, 2444, 2154, 1175]

/-- `ζ^BitRev7(k)`. -/
def zeta (k : Nat) : Zq := ζ ^ bitRev7 k

/-- `γ = ζ^(2BitRev7(i) + 1)`, the modulus of the `i`-th product of
`MultiplyNTTs`. -/
def gamma (i : Nat) : Zq := ζ ^ (2 * bitRev7 i + 1)

theorem zetas_length : zetas.length = 128 := by decide +kernel

theorem gammas_length : gammas.length = 128 := by decide +kernel

/-- Entry `j` of `l` is `f (i + j)`, for each entry: a `List.rec` over `Nat.beq`,
which the kernel evaluates in one pass (rather than `getD` for each index). -/
private noncomputable def listIs (f : Nat → Nat) (l : List Nat) : Nat → Bool :=
  List.rec (fun _ => true) (fun a _ ih i => Nat.beq a (f i) && ih (i + 1)) l

private theorem listIs_spec {f : Nat → Nat} {l : List Nat} {i : Nat} (h : listIs f l i = true) :
    ∀ j < l.length, l.getD j 0 = f (i + j) := by
  induction l generalizing i with
  | nil => intro j hj; simp at hj
  | cons a l ih =>
    simp only [listIs, Bool.and_eq_true] at h
    intro j hj
    cases j with
    | zero => simpa using Nat.eq_of_beq_eq_true h.1
    | succ j =>
      have := ih h.2 j (by simpa using hj)
      rw [show i + (j + 1) = i + 1 + j by omega]
      simpa using this

private theorem zetas_nat : ∀ i < 128, zetas.getD i 0 = 17 ^ bitRev7 i % 3329 := by
  intro i hi
  have := listIs_spec (f := fun i => 17 ^ bitRev7 i % 3329) (l := zetas) (i := 0) (by decide +kernel) i
    (by rw [zetas_length]; exact hi)
  simpa using this

private theorem gammas_nat : ∀ i < 128, gammas.getD i 0 = 17 ^ (2 * bitRev7 i + 1) % 3329 := by
  intro i hi
  have := listIs_spec (f := fun i => 17 ^ (2 * bitRev7 i + 1) % 3329) (l := gammas) (i := 0)
    (by decide +kernel) i (by rw [gammas_length]; exact hi)
  simpa using this

/-- Entry `k` of `zetas` is `ζ^BitRev7(k)`. -/
theorem zetas_getD {k : Nat} (hk : k < 128) : zetas.getD k 0 = (zeta k).val := by
  rw [zetas_nat k hk, zeta, val_pow]; rfl

/-- Entry `i` of `gammas` is `ζ^(2BitRev7(i) + 1)`. -/
theorem gammas_getD {i : Nat} (hi : i < 128) : gammas.getD i 0 = (gamma i).val := by
  rw [gammas_nat i hi, gamma, val_pow]; rfl

theorem zetas_getElem {k : Nat} (hk : k < 128) :
    zetas[k]'(by rw [zetas_length]; exact hk) = (zeta k).val := by
  rw [← zetas_getD hk, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem, Option.getD_some]

theorem gammas_getElem {i : Nat} (hi : i < 128) :
    gammas[i]'(by rw [gammas_length]; exact hi) = (gamma i).val := by
  rw [← gammas_getD hi, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem, Option.getD_some]

theorem zeta_eq {k : Nat} (hk : k < 128) : zeta k = ofNat (zetas.getD k 0) := by
  rw [zetas_getD hk, ofNat_val]

theorem gamma_eq {i : Nat} (hi : i < 128) : gamma i = ofNat (gammas.getD i 0) := by
  rw [gammas_getD hi, ofNat_val]

/-! ## Butterflies -/

/-- The butterfly of Algorithm 9 (lines 8–10) on `f[j]` and `f[j + len]`
with the zeta `z`: `t ← z · f[j + len]`, `f[j + len] ← f[j] - t`,
`f[j] ← f[j] + t`. -/
def bfly (f : Poly) (j len : Nat) (z : Zq) : Poly :=
  let t := z * f[j + len]!
  let g := f.set! (j + len) (f[j]! - t)
  g.set! j (g[j]! + t)

/-- The butterfly of Algorithm 10 (lines 8–10) on `f[j]` and `f[j + len]`
with the zeta `z`: `t ← f[j]`, `f[j] ← t + f[j + len]`,
`f[j + len] ← z · (f[j + len] - t)`. -/
def bflyInv (f : Poly) (j len : Nat) (z : Zq) : Poly :=
  let t := f[j]!
  let g := f.set! j (t + f[j + len]!)
  g.set! (j + len) (z * (g[j + len]! - t))

/-- A butterfly changes `f[j]` to `f[j] + z·f[j + len]` and `f[j + len]` to
`f[j] - z·f[j + len]`, and nothing else. -/
theorem bfly_get (f : Poly) {j len : Nat} (hlen : 0 < len) (hj : j + len < n) (z : Zq)
    {i : Nat} (hi : i < n) :
    (bfly f j len z)[i]! =
      if i = j then f[j]! + z * f[j + len]!
      else if i = j + len then f[j]! - z * f[j + len]!
      else f[i]! := by
  simp only [bfly]
  by_cases h1 : i = j
  · subst h1
    rw [getElem!_set!_self _ hi, getElem!_set!_ne _ hi (by omega), ite_eq_left rfl]
  · rw [getElem!_set!_ne _ hi (Ne.symm h1), ite_eq_right h1]
    by_cases h2 : i = j + len
    · subst h2; rw [getElem!_set!_self _ hi, ite_eq_left rfl]
    · rw [getElem!_set!_ne _ hi (Ne.symm h2), ite_eq_right h2]

/-- An inverse butterfly changes `f[j]` to `f[j] + f[j + len]` and
`f[j + len]` to `z·(f[j + len] - f[j])`, and nothing else. -/
theorem bflyInv_get (f : Poly) {j len : Nat} (hlen : 0 < len) (hj : j + len < n) (z : Zq)
    {i : Nat} (hi : i < n) :
    (bflyInv f j len z)[i]! =
      if i = j then f[j]! + f[j + len]!
      else if i = j + len then z * (f[j + len]! - f[j]!)
      else f[i]! := by
  simp only [bflyInv]
  rw [getElem!_set!_ne _ hj (by omega)]
  by_cases h1 : i = j
  · subst h1
    rw [getElem!_set!_ne _ hi (by omega), getElem!_set!_self _ hi, ite_eq_left rfl]
  · rw [ite_eq_right h1]
    by_cases h2 : i = j + len
    · subst h2; rw [getElem!_set!_self _ hi, ite_eq_left rfl]
    · rw [getElem!_set!_ne _ hi (Ne.symm h2), getElem!_set!_ne _ hi (Ne.symm h1), ite_eq_right h2]

/-! ## Loops -/

theorem foldl_range'_succ {α : Type} (g : α → Nat → α) (x : α) (s t : Nat) :
    (List.range' s (t + 1)).foldl g x = g ((List.range' s t).foldl g x) (s + t) := by
  rw [List.range'_concat, List.foldl_append, Nat.one_mul]; rfl

theorem foldl_range_succ {α : Type} (g : α → Nat → α) (x : α) (t : Nat) :
    (List.range (t + 1)).foldl g x = g ((List.range t).foldl g x) t := by
  rw [List.range_succ, List.foldl_append]; rfl

/-! ## NTT -/

/-- The first `t` iterations of the innermost loop of Algorithm 9 for the
block from `start` of the layer with `len`, whose zeta is `zeta k`. -/
def nttBlockN (f : Poly) (len k start t : Nat) : Poly :=
  (List.range' start t).foldl (fun f j => bfly f j len (zeta k)) f

/-- The innermost loop of Algorithm 9: the `len` butterflies of a block. -/
def nttBlock (f : Poly) (len k start : Nat) : Poly := nttBlockN f len k start len

/-- The first `b` iterations of the middle loop of Algorithm 9 for the layer
with `len`: blocks `0 … b - 1`, block `c` from `2 · len · c` with the zeta
`zeta (128 / len + c)`. -/
def nttLayerN (f : Poly) (len b : Nat) : Poly :=
  (List.range b).foldl (fun f c => nttBlock f len (128 / len + c) (2 * len * c)) f

/-- The middle loop of Algorithm 9: the `128 / len` blocks of the layer with
`len`. -/
def nttLayer (f : Poly) (len : Nat) : Poly := nttLayerN f len (128 / len)

/-- The values of `len` of the layers of Algorithm 9, in order. -/
def nttLens : List Nat := [128, 64, 32, 16, 8, 4, 2]

theorem nttBlockN_zero (f : Poly) (len k start : Nat) : nttBlockN f len k start 0 = f := rfl

theorem nttBlockN_succ (f : Poly) (len k start t : Nat) :
    nttBlockN f len k start (t + 1) = bfly (nttBlockN f len k start t) (start + t) len (zeta k) :=
  foldl_range'_succ _ _ _ _

theorem nttLayerN_zero (f : Poly) (len : Nat) : nttLayerN f len 0 = f := rfl

theorem nttLayerN_succ (f : Poly) (len b : Nat) :
    nttLayerN f len (b + 1) = nttBlock (nttLayerN f len b) len (128 / len + b) (2 * len * b) :=
  foldl_range_succ _ _ _

/-- Each coefficient after the first `t` butterflies of a block: the
butterflies on `(j, j + len)` for `start ≤ j < start + t` are done. -/
theorem nttBlockN_get (f : Poly) {len k start t : Nat} (hlen : 0 < len) (ht : t ≤ len)
    (hs : start + 2 * len ≤ n) {i : Nat} (hi : i < n) :
    (nttBlockN f len k start t)[i]! =
      if start ≤ i ∧ i < start + t then f[i]! + zeta k * f[i + len]!
      else if start + len ≤ i ∧ i < start + len + t then f[i - len]! - zeta k * f[i]!
      else f[i]! := by
  induction t generalizing i with
  | zero =>
    rw [nttBlockN_zero, ite_eq_right (by omega), ite_eq_right (by omega)]
  | succ t ih =>
    rw [nttBlockN_succ, bfly_get _ hlen (by omega) _ hi, ih (i := start + t) (by omega) (by omega),
      ih (i := start + t + len) (by omega) (by omega), ih (by omega) hi]
    rcases (by omega : i < start ∨ (start ≤ i ∧ i < start + t) ∨ i = start + t ∨
        (start + t < i ∧ i < start + len) ∨ (start + len ≤ i ∧ i < start + t + len) ∨
        i = start + t + len ∨ start + t + len < i) with h | h | rfl | h | h | rfl | h <;>
      simp (disch := omega) only [ite_eq_left, ite_eq_right, Nat.add_sub_cancel, ↓reduceIte]

/-- A whole block. -/
theorem nttBlock_get (f : Poly) {len k start : Nat} (hlen : 0 < len) (hs : start + 2 * len ≤ n)
    {i : Nat} (hi : i < n) :
    (nttBlock f len k start)[i]! =
      if start ≤ i ∧ i < start + len then f[i]! + zeta k * f[i + len]!
      else if start + len ≤ i ∧ i < start + 2 * len then f[i - len]! - zeta k * f[i]!
      else f[i]! := by
  rw [nttBlock, nttBlockN_get f hlen (Nat.le_refl _) hs hi, show start + len + len = start + 2 * len by
    omega]

/-- A step of the middle loop of Algorithm 9 with the counter `i`, as the
standard writes it. -/
private def nttMid (len : Nat) (b : Poly × Nat) (start : Nat) : Poly × Nat :=
  (nttBlock b.1 len b.2 start, b.2 + 1)

/-- A step of the outer loop of Algorithm 9 with the counter `i`. -/
private def nttOuter (b : Poly × Nat) (len : Nat) : Poly × Nat :=
  (List.range' 0 (n / (2 * len)) (2 * len)).foldl (nttMid len) b

private theorem ntt_eq_outer (f : Poly) : ntt f = (nttLens.foldl nttOuter (f, 1)).1 := by
  simp only [ntt, Id.run, List.forIn_pure_yield_eq_foldl, bind_pure_comp, map_pure]
  rfl

private theorem foldl_nttMid (len st i : Nat) (f : Poly) :
    ∀ cnt, (List.range' 0 cnt st).foldl (nttMid len) (f, i) =
      ((List.range cnt).foldl (fun g c => nttBlock g len (i + c) (st * c)) f, i + cnt)
  | 0 => rfl
  | cnt + 1 => by
    rw [List.range'_concat, List.foldl_append, foldl_nttMid len st i f cnt, foldl_range_succ,
      Nat.zero_add]
    rfl

private theorem nttOuter_eq (f : Poly) (len i : Nat) :
    nttOuter (f, i) len = ((List.range (n / (2 * len))).foldl
      (fun g c => nttBlock g len (i + c) (2 * len * c)) f, i + n / (2 * len)) :=
  foldl_nttMid _ _ _ _ _

/-- `NTT` is its seven layers, in order. -/
theorem ntt_eq_layers (f : Poly) : ntt f = nttLens.foldl nttLayer f := by
  rw [ntt_eq_outer]
  simp only [nttLens, List.foldl_cons, List.foldl_nil, nttOuter_eq, nttLayer, nttLayerN, n,
    Nat.reduceMul, Nat.reduceDiv, Nat.reduceAdd]

/-- The butterflies of Algorithm 9, in order: `(j, len, k)` for the
butterfly on `f[j]` and `f[j + len]` with the zeta `zeta k`. -/
def nttOps : List (Nat × Nat × Nat) :=
  nttLens.flatMap fun len => (List.range (128 / len)).flatMap fun c =>
    (List.range' (2 * len * c) len).map fun j => (j, len, 128 / len + c)

/-- `NTT` is its 896 butterflies, in order. -/
theorem ntt_eq_ops (f : Poly) : ntt f = nttOps.foldl (fun f o => bfly f o.1 o.2.1 (zeta o.2.2)) f := by
  simp only [ntt_eq_layers, nttOps, List.foldl_flatMap, List.foldl_map]
  rfl

/-! ## NTT⁻¹ -/

/-- The first `t` iterations of the innermost loop of Algorithm 10 for the
block from `start` of the layer with `len`, whose zeta is `zeta k`. -/
def nttInvBlockN (f : Poly) (len k start t : Nat) : Poly :=
  (List.range' start t).foldl (fun f j => bflyInv f j len (zeta k)) f

/-- The innermost loop of Algorithm 10: the `len` butterflies of a block. -/
def nttInvBlock (f : Poly) (len k start : Nat) : Poly := nttInvBlockN f len k start len

/-- The first `b` iterations of the middle loop of Algorithm 10 for the
layer with `len`: blocks `0 … b - 1`, block `c` from `2 · len · c` with the
zeta `zeta (256 / len - 1 - c)`. -/
def nttInvLayerN (f : Poly) (len b : Nat) : Poly :=
  (List.range b).foldl (fun f c => nttInvBlock f len (256 / len - 1 - c) (2 * len * c)) f

/-- The middle loop of Algorithm 10: the `128 / len` blocks of the layer
with `len`. -/
def nttInvLayer (f : Poly) (len : Nat) : Poly := nttInvLayerN f len (128 / len)

/-- The values of `len` of the layers of Algorithm 10, in order. -/
def nttInvLens : List Nat := [2, 4, 8, 16, 32, 64, 128]

theorem nttInvBlockN_zero (f : Poly) (len k start : Nat) : nttInvBlockN f len k start 0 = f := rfl

theorem nttInvBlockN_succ (f : Poly) (len k start t : Nat) :
    nttInvBlockN f len k start (t + 1) =
      bflyInv (nttInvBlockN f len k start t) (start + t) len (zeta k) :=
  foldl_range'_succ _ _ _ _

theorem nttInvLayerN_zero (f : Poly) (len : Nat) : nttInvLayerN f len 0 = f := rfl

theorem nttInvLayerN_succ (f : Poly) (len b : Nat) :
    nttInvLayerN f len (b + 1) =
      nttInvBlock (nttInvLayerN f len b) len (256 / len - 1 - b) (2 * len * b) :=
  foldl_range_succ _ _ _

/-- Each coefficient after the first `t` inverse butterflies of a block. -/
theorem nttInvBlockN_get (f : Poly) {len k start t : Nat} (hlen : 0 < len) (ht : t ≤ len)
    (hs : start + 2 * len ≤ n) {i : Nat} (hi : i < n) :
    (nttInvBlockN f len k start t)[i]! =
      if start ≤ i ∧ i < start + t then f[i]! + f[i + len]!
      else if start + len ≤ i ∧ i < start + len + t then zeta k * (f[i]! - f[i - len]!)
      else f[i]! := by
  induction t generalizing i with
  | zero =>
    rw [nttInvBlockN_zero, ite_eq_right (by omega), ite_eq_right (by omega)]
  | succ t ih =>
    rw [nttInvBlockN_succ, bflyInv_get _ hlen (by omega) _ hi, ih (i := start + t) (by omega) (by omega),
      ih (i := start + t + len) (by omega) (by omega), ih (by omega) hi]
    rcases (by omega : i < start ∨ (start ≤ i ∧ i < start + t) ∨ i = start + t ∨
        (start + t < i ∧ i < start + len) ∨ (start + len ≤ i ∧ i < start + t + len) ∨
        i = start + t + len ∨ start + t + len < i) with h | h | rfl | h | h | rfl | h <;>
      simp (disch := omega) only [ite_eq_left, ite_eq_right, Nat.add_sub_cancel, ↓reduceIte]

/-- A whole inverse block. -/
theorem nttInvBlock_get (f : Poly) {len k start : Nat} (hlen : 0 < len) (hs : start + 2 * len ≤ n)
    {i : Nat} (hi : i < n) :
    (nttInvBlock f len k start)[i]! =
      if start ≤ i ∧ i < start + len then f[i]! + f[i + len]!
      else if start + len ≤ i ∧ i < start + 2 * len then zeta k * (f[i]! - f[i - len]!)
      else f[i]! := by
  rw [nttInvBlock, nttInvBlockN_get f hlen (Nat.le_refl _) hs hi,
    show start + len + len = start + 2 * len by omega]

/-- A step of the middle loop of Algorithm 10 with the counter `i`, as the
standard writes it. -/
private def nttInvMid (len : Nat) (b : Poly × Nat) (start : Nat) : Poly × Nat :=
  (nttInvBlock b.1 len b.2 start, b.2 - 1)

/-- A step of the outer loop of Algorithm 10 with the counter `i`. -/
private def nttInvOuter (b : Poly × Nat) (len : Nat) : Poly × Nat :=
  (List.range' 0 (n / (2 * len)) (2 * len)).foldl (nttInvMid len) b

private theorem nttInv_eq_outer (f : Poly) :
    nttInv f = ((nttInvLens.foldl nttInvOuter (f, 127)).1).map (· * 3303) := by
  simp only [nttInv, Id.run, List.forIn_pure_yield_eq_foldl, bind_pure_comp, map_pure]
  rfl

private theorem foldl_nttInvMid (len st i : Nat) (f : Poly) :
    ∀ cnt, (List.range' 0 cnt st).foldl (nttInvMid len) (f, i) =
      ((List.range cnt).foldl (fun g c => nttInvBlock g len (i - c) (st * c)) f, i - cnt)
  | 0 => rfl
  | cnt + 1 => by
    rw [List.range'_concat, List.foldl_append, foldl_nttInvMid len st i f cnt, foldl_range_succ,
      Nat.zero_add]
    rfl

private theorem nttInvOuter_eq (f : Poly) (len i : Nat) :
    nttInvOuter (f, i) len = ((List.range (n / (2 * len))).foldl
      (fun g c => nttInvBlock g len (i - c) (2 * len * c)) f, i - n / (2 * len)) :=
  foldl_nttInvMid _ _ _ _ _

/-- `NTT⁻¹` is its seven layers, in order, and the multiplication of every
coefficient by `3303 = 128⁻¹ mod q`. -/
theorem nttInv_eq_layers (f : Poly) :
    nttInv f = (nttInvLens.foldl nttInvLayer f).map (· * 3303) := by
  rw [nttInv_eq_outer]
  simp only [nttInvLens, List.foldl_cons, List.foldl_nil, nttInvOuter_eq, nttInvLayer,
    nttInvLayerN, n, Nat.reduceMul, Nat.reduceDiv, Nat.reduceSub]

/-- The butterflies of Algorithm 10, in order: `(j, len, k)` for the
inverse butterfly on `f[j]` and `f[j + len]` with the zeta `zeta k`. -/
def nttInvOps : List (Nat × Nat × Nat) :=
  nttInvLens.flatMap fun len => (List.range (128 / len)).flatMap fun c =>
    (List.range' (2 * len * c) len).map fun j => (j, len, 256 / len - 1 - c)

/-- `NTT⁻¹` is its 896 butterflies, in order, and the multiplication by
3303. -/
theorem nttInv_eq_ops (f : Poly) :
    nttInv f = (nttInvOps.foldl (fun f o => bflyInv f o.1 o.2.1 (zeta o.2.2)) f).map (· * 3303) := by
  simp only [nttInv_eq_layers, nttInvOps, List.foldl_flatMap, List.foldl_map]
  rfl

/-- The last step of `NTT⁻¹`, coefficient by coefficient. -/
theorem map_mul_get (f : Poly) {i : Nat} (hi : i < n) : (f.map (· * 3303))[i]! = f[i]! * 3303 := by
  rw [getElem!_eq _ hi, getElem!_eq _ hi, Vector.getElem_map]

/-! ## Blocks, some butterflies at a time -/

theorem nttBlockN_add (f : Poly) (len k start t t' : Nat) :
    nttBlockN f len k start (t + t') = nttBlockN (nttBlockN f len k start t) len k (start + t) t' := by
  simp only [nttBlockN]; rw [← List.foldl_append, List.range'_append_1]

theorem nttInvBlockN_add (f : Poly) (len k start t t' : Nat) :
    nttInvBlockN f len k start (t + t') =
      nttInvBlockN (nttInvBlockN f len k start t) len k (start + t) t' := by
  simp only [nttInvBlockN]; rw [← List.foldl_append, List.range'_append_1]

/-- `nttBlockN_get`, for the butterflies of the block up to `start + t`
only. -/
theorem nttBlockN_get' (f : Poly) {len k start t : Nat} (hlen : 0 < len) (ht : t ≤ len)
    (hs : start + len + t ≤ n) {i : Nat} (hi : i < n) :
    (nttBlockN f len k start t)[i]! =
      if start ≤ i ∧ i < start + t then f[i]! + zeta k * f[i + len]!
      else if start + len ≤ i ∧ i < start + len + t then f[i - len]! - zeta k * f[i]!
      else f[i]! := by
  induction t generalizing i with
  | zero =>
    rw [nttBlockN_zero, ite_eq_right (by omega), ite_eq_right (by omega)]
  | succ t ih =>
    rw [nttBlockN_succ, bfly_get _ hlen (by omega) _ hi, ih (i := start + t) (by omega) (by omega) (by omega),
      ih (i := start + t + len) (by omega) (by omega) (by omega), ih (by omega) (by omega) hi]
    rcases (by omega : i < start ∨ (start ≤ i ∧ i < start + t) ∨ i = start + t ∨
        (start + t < i ∧ i < start + len) ∨ (start + len ≤ i ∧ i < start + t + len) ∨
        i = start + t + len ∨ start + t + len < i) with h | h | rfl | h | h | rfl | h <;>
      simp (disch := omega) only [ite_eq_left, ite_eq_right, Nat.add_sub_cancel, ↓reduceIte]

theorem nttInvBlockN_get' (f : Poly) {len k start t : Nat} (hlen : 0 < len) (ht : t ≤ len)
    (hs : start + len + t ≤ n) {i : Nat} (hi : i < n) :
    (nttInvBlockN f len k start t)[i]! =
      if start ≤ i ∧ i < start + t then f[i]! + f[i + len]!
      else if start + len ≤ i ∧ i < start + len + t then zeta k * (f[i]! - f[i - len]!)
      else f[i]! := by
  induction t generalizing i with
  | zero =>
    rw [nttInvBlockN_zero, ite_eq_right (by omega), ite_eq_right (by omega)]
  | succ t ih =>
    rw [nttInvBlockN_succ, bflyInv_get _ hlen (by omega) _ hi,
      ih (i := start + t) (by omega) (by omega) (by omega),
      ih (i := start + t + len) (by omega) (by omega) (by omega), ih (by omega) (by omega) hi]
    rcases (by omega : i < start ∨ (start ≤ i ∧ i < start + t) ∨ i = start + t ∨
        (start + t < i ∧ i < start + len) ∨ (start + len ≤ i ∧ i < start + t + len) ∨
        i = start + t + len ∨ start + t + len < i) with h | h | rfl | h | h | rfl | h <;>
      simp (disch := omega) only [ite_eq_left, ite_eq_right, Nat.add_sub_cancel, ↓reduceIte]

/-! ## MultiplyNTTs -/

/-- Coefficient `2i` of `MultiplyNTTs(f, g)`: `f[2i]·g[2i] + f[2i+1]·g[2i+1]·γᵢ`. -/
theorem multiplyNTTs_even (f g : Poly) {i : Nat} (hi : i < 128) :
    (multiplyNTTs f g)[2 * i]! =
      f[2 * i]! * g[2 * i]! + f[2 * i + 1]! * g[2 * i + 1]! * gamma i := by
  rw [getElem!_eq _ (by rw [n_eq]; omega), multiplyNTTs, Vector.getElem_ofFn]
  dsimp only
  rw [show 2 * i / 2 = i by omega, ite_eq_left (show 2 * i % 2 = 0 by omega)]
  rfl

/-- Coefficient `2i + 1` of `MultiplyNTTs(f, g)`: `f[2i]·g[2i+1] + f[2i+1]·g[2i]`. -/
theorem multiplyNTTs_odd (f g : Poly) {i : Nat} (hi : i < 128) :
    (multiplyNTTs f g)[2 * i + 1]! = f[2 * i]! * g[2 * i + 1]! + f[2 * i + 1]! * g[2 * i]! := by
  rw [getElem!_eq _ (by rw [n_eq]; omega), multiplyNTTs, Vector.getElem_ofFn]
  dsimp only
  rw [show (2 * i + 1) / 2 = i by omega, ite_eq_right (show ¬ (2 * i + 1) % 2 = 0 by omega)]
  rfl

/-- Any coefficient of `MultiplyNTTs(f, g)`. -/
theorem multiplyNTTs_get (f g : Poly) {h : Nat} (hh : h < n) :
    (multiplyNTTs f g)[h]! =
      if h % 2 = 0 then
        f[h]! * g[h]! + f[h + 1]! * g[h + 1]! * gamma (h / 2)
      else f[h - 1]! * g[h]! + f[h]! * g[h - 1]! := by
  rw [n_eq] at hh
  split
  · have := multiplyNTTs_even f g (i := h / 2) (by omega)
    rwa [show 2 * (h / 2) = h by omega] at this
  · have := multiplyNTTs_odd f g (i := h / 2) (by omega)
    rwa [show 2 * (h / 2) + 1 = h by omega, show 2 * (h / 2) = h - 1 by omega] at this

end VG.Proof.MlKem
