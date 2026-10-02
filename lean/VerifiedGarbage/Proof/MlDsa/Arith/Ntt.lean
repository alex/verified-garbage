import VerifiedGarbage.Proof.MlDsa.Arith.Zq

/-!
# ML-DSA: the NTT as butterflies, for every target

`NTT` (Algorithm 41) and `NTT⁻¹` (Algorithm 42) restated as the loops an
implementation runs, so that its proof is only about its instructions:

* the zetas `zetas m = ζ^BitRev8(m) mod q` as numbers (`zetaNat`);
* one butterfly, `bfly` (Algorithm 41, lines 8–10) or `bflyInv` (Algorithm
  42, lines 8–11), and what it does to each coefficient (`bfly_get`,
  `bflyInv_get`);
* the three nested loops: `ntt f` is `nttLayer` for each `len` of `nttLens`,
  a layer is `blockN` for each of its blocks (`layerN`), and a block is
  `len` butterflies. `blockN` and `layerN` are the loops after their first
  `t` iterations (`…_zero`, `…_succ`), for loop invariants, and
  `blockN_bfly_get` and `blockN_bflyInv_get` say what each coefficient is
  after `t` butterflies of a block. `nttInv f` is likewise `nttInvLayer` for
  each `len` of `nttInvLens`, then the multiplication of every coefficient
  by `256⁻¹ = 8347681`.

The zeta of block `c` of the layer with `len` is `zetas (128 / len + c)` in
`NTT` (the standard's counter `m` runs from 1 up) and
`-zetas (256 / len - 1 - c)` in `NTT⁻¹` (from 255 down).
-/

namespace VG.Proof.MlDsa.Arith

open VG.Spec.MlDsa

/-! ## The zetas -/

/-- `ζ^BitRev8(m) mod q`, as a number. -/
def zetaNat (m : Nat) : Nat := 1753 ^ bitRev8 m % 8380417

theorem zetaNat_eq (m : Nat) : zetaNat m = (zetas m).val := by
  rw [zetas, val_pow]; rfl

theorem zetaNat_lt (m : Nat) : zetaNat m < q := Nat.mod_lt _ (by decide)

/-- `-ζ^BitRev8(m) mod q`, as a number: the zeta of `NTT⁻¹`. -/
def negZetaNat (m : Nat) : Nat := (8380417 - zetaNat m) % 8380417

theorem negZetaNat_eq (m : Nat) : negZetaNat m = (-zetas m).val := by
  rw [val_neg, ← zetaNat_eq]; rfl

theorem negZetaNat_lt (m : Nat) : negZetaNat m < q := Nat.mod_lt _ (by decide)

/-! ## Butterflies -/

/-- The butterfly of Algorithm 41 (lines 8–10) on `w[j]` and `w[j + len]`
with the zeta `z`: `t ← z · w[j + len]`, `w[j + len] ← w[j] - t`,
`w[j] ← w[j] + t`. -/
def bfly (w : Poly) (j len : Nat) (z : Zq) : Poly :=
  let t := z * w[j + len]!
  let w := w.set! (j + len) (w[j]! - t)
  w.set! j (w[j]! + t)

/-- The butterfly of Algorithm 42 (lines 8–11) on `w[j]` and `w[j + len]`
with the zeta `z`: `t ← w[j]`, `w[j] ← t + w[j + len]`,
`w[j + len] ← t - w[j + len]`, `w[j + len] ← z · w[j + len]`. -/
def bflyInv (w : Poly) (j len : Nat) (z : Zq) : Poly :=
  let t := w[j]!
  let w := w.set! j (t + w[j + len]!)
  let w := w.set! (j + len) (t - w[j + len]!)
  w.set! (j + len) (z * w[j + len]!)

/-- A butterfly changes `w[j]` to `w[j] + z·w[j + len]` and `w[j + len]` to
`w[j] - z·w[j + len]`, and nothing else. -/
theorem bfly_get (w : Poly) {j len : Nat} (hlen : 0 < len) (hj : j + len < n) (z : Zq)
    {i : Nat} (hi : i < n) :
    (bfly w j len z)[i]! =
      if i = j then w[j]! + z * w[j + len]!
      else if i = j + len then w[j]! - z * w[j + len]!
      else w[i]! := by
  simp only [bfly]
  by_cases h1 : i = j
  · subst h1
    rw [getElem!_set!_self _ hi, getElem!_set!_ne _ hi (by omega), ite_eq_left rfl]
  · rw [getElem!_set!_ne _ hi (Ne.symm h1), ite_eq_right h1]
    by_cases h2 : i = j + len
    · subst h2; rw [getElem!_set!_self _ hi, ite_eq_left rfl]
    · rw [getElem!_set!_ne _ hi (Ne.symm h2), ite_eq_right h2]

/-- An inverse butterfly changes `w[j]` to `w[j] + w[j + len]` and
`w[j + len]` to `z·(w[j] - w[j + len])`, and nothing else. -/
theorem bflyInv_get (w : Poly) {j len : Nat} (hlen : 0 < len) (hj : j + len < n) (z : Zq)
    {i : Nat} (hi : i < n) :
    (bflyInv w j len z)[i]! =
      if i = j then w[j]! + w[j + len]!
      else if i = j + len then z * (w[j]! - w[j + len]!)
      else w[i]! := by
  simp only [bflyInv]
  rw [getElem!_set!_self _ hj, getElem!_set!_ne _ hj (by omega)]
  by_cases h1 : i = j
  · subst h1
    rw [getElem!_set!_ne _ hi (by omega), getElem!_set!_ne _ hi (by omega), getElem!_set!_self _ hi,
      ite_eq_left rfl]
  · rw [ite_eq_right h1]
    by_cases h2 : i = j + len
    · subst h2; rw [getElem!_set!_self _ hi, ite_eq_left rfl]
    · rw [getElem!_set!_ne _ hi (Ne.symm h2), getElem!_set!_ne _ hi (Ne.symm h2),
        getElem!_set!_ne _ hi (Ne.symm h1), ite_eq_right h2]

/-! ## Loops -/

theorem foldl_range'_succ {α : Type} (g : α → Nat → α) (x : α) (s t : Nat) :
    (List.range' s (t + 1)).foldl g x = g ((List.range' s t).foldl g x) (s + t) := by
  rw [List.range'_concat, List.foldl_append, Nat.one_mul]; rfl

theorem foldl_range_succ {α : Type} (g : α → Nat → α) (x : α) (t : Nat) :
    (List.range (t + 1)).foldl g x = g ((List.range t).foldl g x) t := by
  rw [List.range_succ, List.foldl_append]; rfl

/-- The first `t` iterations of the innermost loop for the block from
`start` of the layer with `len`: the butterflies `op` with the zeta `z`. -/
def blockN (op : Poly → Nat → Nat → Zq → Poly) (w : Poly) (len : Nat) (z : Zq) (start t : Nat) : Poly :=
  (List.range' start t).foldl (fun w j => op w j len z) w

/-- The first `b` iterations of the middle loop for the layer with `len`:
blocks `0 … b - 1`, block `c` from `2 · len · c` with the zeta `zf c`. -/
def layerN (op : Poly → Nat → Nat → Zq → Poly) (w : Poly) (len : Nat) (zf : Nat → Zq) (b : Nat) : Poly :=
  (List.range b).foldl (fun w c => blockN op w len (zf c) (2 * len * c) len) w

theorem blockN_zero (op : Poly → Nat → Nat → Zq → Poly) (w : Poly) (len : Nat) (z : Zq) (start : Nat) :
    blockN op w len z start 0 = w := rfl

theorem blockN_succ (op : Poly → Nat → Nat → Zq → Poly) (w : Poly) (len : Nat) (z : Zq) (start t : Nat) :
    blockN op w len z start (t + 1) = op (blockN op w len z start t) (start + t) len z :=
  foldl_range'_succ _ _ _ _

theorem layerN_zero (op : Poly → Nat → Nat → Zq → Poly) (w : Poly) (len : Nat) (zf : Nat → Zq) :
    layerN op w len zf 0 = w := rfl

theorem layerN_succ (op : Poly → Nat → Nat → Zq → Poly) (w : Poly) (len : Nat) (zf : Nat → Zq) (b : Nat) :
    layerN op w len zf (b + 1) = blockN op (layerN op w len zf b) len (zf b) (2 * len * b) len :=
  foldl_range_succ _ _ _

/-- Each coefficient after the first `t` butterflies of a block of `NTT`:
the butterflies on `(j, j + len)` for `start ≤ j < start + t` are done. -/
theorem blockN_bfly_get (w : Poly) {len : Nat} {z : Zq} {start t : Nat} (hlen : 0 < len) (ht : t ≤ len)
    (hs : start + 2 * len ≤ n) {i : Nat} (hi : i < n) :
    (blockN bfly w len z start t)[i]! =
      if start ≤ i ∧ i < start + t then w[i]! + z * w[i + len]!
      else if start + len ≤ i ∧ i < start + len + t then w[i - len]! - z * w[i]!
      else w[i]! := by
  induction t generalizing i with
  | zero =>
    rw [blockN_zero, ite_eq_right (by omega), ite_eq_right (by omega)]
  | succ t ih =>
    rw [blockN_succ, bfly_get _ hlen (by omega) _ hi, ih (i := start + t) (by omega) (by omega),
      ih (i := start + t + len) (by omega) (by omega), ih (by omega) hi]
    rcases (by omega : i < start ∨ (start ≤ i ∧ i < start + t) ∨ i = start + t ∨
        (start + t < i ∧ i < start + len) ∨ (start + len ≤ i ∧ i < start + t + len) ∨
        i = start + t + len ∨ start + t + len < i) with h | h | rfl | h | h | rfl | h <;>
      simp (disch := omega) only [ite_eq_left, ite_eq_right, Nat.add_sub_cancel, ↓reduceIte]

/-- Each coefficient after the first `t` inverse butterflies of a block of
`NTT⁻¹`. -/
theorem blockN_bflyInv_get (w : Poly) {len : Nat} {z : Zq} {start t : Nat} (hlen : 0 < len) (ht : t ≤ len)
    (hs : start + 2 * len ≤ n) {i : Nat} (hi : i < n) :
    (blockN bflyInv w len z start t)[i]! =
      if start ≤ i ∧ i < start + t then w[i]! + w[i + len]!
      else if start + len ≤ i ∧ i < start + len + t then z * (w[i - len]! - w[i]!)
      else w[i]! := by
  induction t generalizing i with
  | zero =>
    rw [blockN_zero, ite_eq_right (by omega), ite_eq_right (by omega)]
  | succ t ih =>
    rw [blockN_succ, bflyInv_get _ hlen (by omega) _ hi, ih (i := start + t) (by omega) (by omega),
      ih (i := start + t + len) (by omega) (by omega), ih (by omega) hi]
    rcases (by omega : i < start ∨ (start ≤ i ∧ i < start + t) ∨ i = start + t ∨
        (start + t < i ∧ i < start + len) ∨ (start + len ≤ i ∧ i < start + t + len) ∨
        i = start + t + len ∨ start + t + len < i) with h | h | rfl | h | h | rfl | h <;>
      simp (disch := omega) only [ite_eq_left, ite_eq_right, Nat.add_sub_cancel, ↓reduceIte]

/-! ## NTT -/

/-- The values of `len` of the layers of Algorithm 41, in order. -/
def nttLens : List Nat := [128, 64, 32, 16, 8, 4, 2, 1]

/-- The middle loop of Algorithm 41: the `128 / len` blocks of the layer
with `len`, block `c` with the zeta `zetas (128 / len + c)`. -/
def nttLayer (w : Poly) (len : Nat) : Poly := layerN bfly w len (fun c => zetas (128 / len + c)) (128 / len)

/-- A step of the middle loop of Algorithm 41 with the counter `m`, as the
standard writes it. -/
private def nttMid (len : Nat) (b : Poly × Nat) (start : Nat) : Poly × Nat :=
  (blockN bfly b.1 len (zetas (b.2 + 1)) start len, b.2 + 1)

/-- A step of the outer loop of Algorithm 41 with the counter `m`. -/
private def nttOuter (b : Poly × Nat) (len : Nat) : Poly × Nat :=
  (List.range' 0 (n / (2 * len)) (2 * len)).foldl (nttMid len) b

private theorem ntt_eq_outer (w : Poly) : ntt w = (nttLens.foldl nttOuter (w, 0)).1 := by
  simp only [ntt, Id.run, List.forIn_pure_yield_eq_foldl, bind_pure_comp, map_pure]
  apply congrArg Prod.fst
  apply congrArg (List.foldl · _ _)
  funext b len
  unfold nttOuter
  rfl

private theorem foldl_nttMid (len st m : Nat) (w : Poly) :
    ∀ cnt, (List.range' 0 cnt st).foldl (nttMid len) (w, m) =
      ((List.range cnt).foldl (fun g c => blockN bfly g len (zetas (m + 1 + c)) (st * c) len) w, m + cnt)
  | 0 => rfl
  | cnt + 1 => by
    rw [List.range'_concat, List.foldl_append, foldl_nttMid len st m w cnt, foldl_range_succ,
      Nat.zero_add]
    show (blockN bfly _ len (zetas (m + cnt + 1)) (st * cnt) len, m + cnt + 1) = _
    rw [Nat.add_right_comm m cnt 1]
    exact Prod.ext rfl (by omega)

private theorem nttOuter_eq (w : Poly) (len m : Nat) :
    nttOuter (w, m) len = ((List.range (n / (2 * len))).foldl
      (fun g c => blockN bfly g len (zetas (m + 1 + c)) (2 * len * c) len) w, m + n / (2 * len)) :=
  foldl_nttMid _ _ _ _ _

/-- `NTT` is its eight layers, in order. -/
theorem ntt_eq_layers (w : Poly) : ntt w = nttLens.foldl nttLayer w := by
  rw [ntt_eq_outer]
  simp only [nttLens, List.foldl_cons, List.foldl_nil, nttOuter_eq, nttLayer, layerN, n,
    Nat.reduceMul, Nat.reduceDiv, Nat.reduceAdd]

/-! ## NTT⁻¹ -/

/-- The values of `len` of the layers of Algorithm 42, in order. -/
def nttInvLens : List Nat := [1, 2, 4, 8, 16, 32, 64, 128]

/-- The middle loop of Algorithm 42: the `128 / len` blocks of the layer
with `len`, block `c` with the zeta `-zetas (256 / len - 1 - c)`. -/
def nttInvLayer (w : Poly) (len : Nat) : Poly :=
  layerN bflyInv w len (fun c => -zetas (256 / len - 1 - c)) (128 / len)

/-- A step of the middle loop of Algorithm 42 with the counter `m`, as the
standard writes it. -/
private def nttInvMid (len : Nat) (b : Poly × Nat) (start : Nat) : Poly × Nat :=
  (blockN bflyInv b.1 len (-zetas (b.2 - 1)) start len, b.2 - 1)

/-- A step of the outer loop of Algorithm 42 with the counter `m`. -/
private def nttInvOuter (b : Poly × Nat) (len : Nat) : Poly × Nat :=
  (List.range' 0 (n / (2 * len)) (2 * len)).foldl (nttInvMid len) b

private theorem nttInv_eq_outer (w : Poly) :
    nttInv w = ((nttInvLens.foldl nttInvOuter (w, 256)).1).map (· * 8347681) := by
  simp only [nttInv, Id.run, List.forIn_pure_yield_eq_foldl, bind_pure_comp, map_pure]
  apply congrArg (fun v => Vector.map _ (Prod.fst v))
  apply congrArg (List.foldl · _ _)
  funext b len
  unfold nttInvOuter
  rfl

private theorem foldl_nttInvMid (len st m : Nat) (w : Poly) :
    ∀ cnt, (List.range' 0 cnt st).foldl (nttInvMid len) (w, m) =
      ((List.range cnt).foldl (fun g c => blockN bflyInv g len (-zetas (m - 1 - c)) (st * c) len) w, m - cnt)
  | 0 => rfl
  | cnt + 1 => by
    rw [List.range'_concat, List.foldl_append, foldl_nttInvMid len st m w cnt, foldl_range_succ,
      Nat.zero_add]
    show (blockN bflyInv _ len (-zetas (m - cnt - 1)) (st * cnt) len, m - cnt - 1) = _
    rw [Nat.sub_sub, Nat.sub_sub, Nat.add_comm cnt 1]

private theorem nttInvOuter_eq (w : Poly) (len m : Nat) :
    nttInvOuter (w, m) len = ((List.range (n / (2 * len))).foldl
      (fun g c => blockN bflyInv g len (-zetas (m - 1 - c)) (2 * len * c) len) w, m - n / (2 * len)) :=
  foldl_nttInvMid _ _ _ _ _

/-- `NTT⁻¹` is its eight layers, in order, and the multiplication of every
coefficient by `8347681 = 256⁻¹ mod q`. -/
theorem nttInv_eq_layers (w : Poly) :
    nttInv w = (nttInvLens.foldl nttInvLayer w).map (· * 8347681) := by
  rw [nttInv_eq_outer]
  simp only [nttInvLens, List.foldl_cons, List.foldl_nil, nttInvOuter_eq, nttInvLayer,
    layerN, n, Nat.reduceMul, Nat.reduceDiv, Nat.reduceSub]

end VG.Proof.MlDsa.Arith
