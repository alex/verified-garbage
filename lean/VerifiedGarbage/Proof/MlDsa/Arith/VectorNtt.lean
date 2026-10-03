import VerifiedGarbage.Proof.MlDsa.Arith.Ntt

/-! Block identities shared by vector NTT implementations. -/
namespace VG.Proof.MlDsa.Arith
open VG.Spec.MlDsa (q n Poly Zq zetas)

/-- The first `t` butterflies of a block of the specification, with the
zeta of index `k` of the table, do `op` to `(j, j + len)`. -/
structure BlkOk (blk : Poly → Nat → Nat → Nat → Nat → Poly) (op : Zq → Zq → Zq → Zq × Zq) : Prop where
  zero : ∀ f len k st, blk f len k st 0 = f
  add : ∀ f len k st t t', blk f len k st (t + t') = blk (blk f len k st t) len k (st + t) t'
  get : ∀ f len k st t, 0 < len → t ≤ len → st + len + t ≤ n → ∀ i < n,
    (blk f len k st t)[i]! = if st ≤ i ∧ i < st + t then (op f[i]! f[i + len]! (zetas k)).1
      else if st + len ≤ i ∧ i < st + len + t then (op f[i - len]! f[i]! (zetas k)).2 else f[i]!

theorem blockN_add (op : Poly → Nat → Nat → Zq → Poly) (f : Poly) (len : Nat) (z : Zq) (st t t' : Nat) :
    blockN op f len z st (t + t') = blockN op (blockN op f len z st t) len z (st + t) t' := by
  simp only [blockN]; rw [← List.foldl_append, List.range'_append_1]

/-- `blockN_bfly_get`, for the butterflies of the block up to `start + t`
only. -/
theorem blockN_bfly_get' (w : Poly) {len : Nat} {z : Zq} {start t : Nat} (hlen : 0 < len) (ht : t ≤ len)
    (hs : start + len + t ≤ n) {i : Nat} (hi : i < n) :
    (blockN bfly w len z start t)[i]! =
      if start ≤ i ∧ i < start + t then w[i]! + z * w[i + len]!
      else if start + len ≤ i ∧ i < start + len + t then w[i - len]! - z * w[i]!
      else w[i]! := by
  induction t generalizing i with
  | zero =>
    rw [blockN_zero, ite_eq_right (by omega), ite_eq_right (by omega)]
  | succ t ih =>
    rw [blockN_succ, bfly_get _ hlen (by omega) _ hi, ih (i := start + t) (by omega) (by omega) (by omega),
      ih (i := start + t + len) (by omega) (by omega) (by omega), ih (by omega) (by omega) hi]
    rcases (by omega : i < start ∨ (start ≤ i ∧ i < start + t) ∨ i = start + t ∨
        (start + t < i ∧ i < start + len) ∨ (start + len ≤ i ∧ i < start + t + len) ∨
        i = start + t + len ∨ start + t + len < i) with h | h | rfl | h | h | rfl | h <;>
      simp (disch := omega) only [ite_eq_left, ite_eq_right, Nat.add_sub_cancel, ↓reduceIte]

/-- `blockN_bflyInv_get`, for the butterflies of the block up to
`start + t` only. -/
theorem blockN_bflyInv_get' (w : Poly) {len : Nat} {z : Zq} {start t : Nat} (hlen : 0 < len) (ht : t ≤ len)
    (hs : start + len + t ≤ n) {i : Nat} (hi : i < n) :
    (blockN bflyInv w len z start t)[i]! =
      if start ≤ i ∧ i < start + t then w[i]! + w[i + len]!
      else if start + len ≤ i ∧ i < start + len + t then z * (w[i - len]! - w[i]!)
      else w[i]! := by
  induction t generalizing i with
  | zero =>
    rw [blockN_zero, ite_eq_right (by omega), ite_eq_right (by omega)]
  | succ t ih =>
    rw [blockN_succ, bflyInv_get _ hlen (by omega) _ hi, ih (i := start + t) (by omega) (by omega) (by omega),
      ih (i := start + t + len) (by omega) (by omega) (by omega), ih (by omega) (by omega) hi]
    rcases (by omega : i < start ∨ (start ≤ i ∧ i < start + t) ∨ i = start + t ∨
        (start + t < i ∧ i < start + len) ∨ (start + len ≤ i ∧ i < start + t + len) ∨
        i = start + t + len ∨ start + t + len < i) with h | h | rfl | h | h | rfl | h <;>
      simp (disch := omega) only [ite_eq_left, ite_eq_right, Nat.add_sub_cancel, ↓reduceIte]

theorem nttBlk_ok : BlkOk (fun f len k st t => blockN bfly f len (zetas k) st t)
    (fun x y z => (x + z * y, x - z * y)) :=
  ⟨fun _ _ _ _ => rfl, fun _ _ _ _ _ _ => blockN_add _ _ _ _ _ _ _,
    fun f _ _ _ _ hl ht hs _ hi => blockN_bfly_get' f hl ht hs hi⟩

/-- Algorithm 42 multiplies by `-ζ`; `vibfly` by `ζ`, the other way round. -/
theorem neg_mul_sub (z x y : Zq) : -z * (x - y) = z * (y - x) := by
  grind

theorem nttInvBlk_ok : BlkOk (fun f len k st t => blockN bflyInv f len (-zetas k) st t)
    (fun x y z => (x + y, z * (y - x))) :=
  ⟨fun _ _ _ _ => rfl, fun _ _ _ _ _ _ => blockN_add _ _ _ _ _ _ _,
    fun f _ _ _ _ hl ht hs _ hi => by rw [blockN_bflyInv_get' f hl ht hs hi, neg_mul_sub]⟩

/-- The first `b` blocks of the layer with `len`, block `c` with the zeta of
index `zi c`. -/
def layF (blk : Poly → Nat → Nat → Nat → Nat → Poly) (F : Poly) (len : Nat) (zi : Nat → Nat) (b : Nat) :
    Poly :=
  (List.range b).foldl (fun f c => blk f len (zi c) (2 * len * c) len) F

/-- Each coefficient after the first `b` blocks of the layer with `len = 1`. -/
theorem layF1_get {blk : Poly → Nat → Nat → Nat → Nat → Poly}
    {op : Zq → Zq → Zq → Zq × Zq} (hblk : BlkOk blk op) (F : Poly) (zi : Nat → Nat) {b : Nat} (hb : b ≤ 128) {j : Nat} (hj : j < 256) :
    (layF blk F 1 zi b)[j]! = if j < 2 * b then
      (if j % 2 = 0 then (op F[j]! F[j + 1]! (zetas (zi (j / 2)))).1
        else (op F[j - 1]! F[j]! (zetas (zi (j / 2)))).2) else F[j]! := by
  induction b generalizing j with
  | zero => rw [ite_eq_right (by omega)]; rfl
  | succ b ih =>
    rw [layF, foldl_range_succ, ← layF,
      hblk.get _ 1 _ _ 1 (by decide) (by decide) (by rw [n_eq]; omega) j (by rw [n_eq]; exact hj)]
    by_cases h1 : 2 * 1 * b ≤ j ∧ j < 2 * 1 * b + 1
    · rw [ite_eq_left h1, ih (by omega) hj, ih (by omega) (by omega), show j / 2 = b by omega]
      simp (disch := omega) only [ite_eq_left, ite_eq_right]
    · rw [ite_eq_right h1]
      by_cases h2 : 2 * 1 * b + 1 ≤ j ∧ j < 2 * 1 * b + 1 + 1
      · rw [ite_eq_left h2, ih (by omega) (by omega), ih (by omega) hj, show j / 2 = b by omega]
        simp (disch := omega) only [ite_eq_left, ite_eq_right]
      · rw [ite_eq_right h2, ih (by omega) hj]
        by_cases h3 : j < 2 * b <;> simp (disch := omega) only [ite_eq_left, ite_eq_right]


/-- Each coefficient after the first `b` blocks of a length-two layer. -/
theorem layF2_get {blk : Poly → Nat → Nat → Nat → Nat → Poly}
    {op : Zq → Zq → Zq → Zq × Zq} (hblk : BlkOk blk op) (F : Poly) (zi : Nat → Nat)
    {b : Nat} (hb : b ≤ 64) {j : Nat} (hj : j < 256) :
    (layF blk F 2 zi b)[j]! = if j < 4*b then
      (if j%4 < 2 then (op F[j]! F[j+2]! (zetas (zi (j/4)))).1
       else (op F[j-2]! F[j]! (zetas (zi (j/4)))).2) else F[j]! := by
  induction b generalizing j with
  | zero => rw [ite_eq_right (by omega)]; rfl
  | succ b ih =>
    rw [layF,foldl_range_succ,← layF,
      hblk.get _ 2 _ _ 2 (by decide) (by decide) (by rw [n_eq]; omega) j (by rw [n_eq]; exact hj)]
    by_cases h1 : 2*2*b ≤ j ∧ j < 2*2*b+2
    · rw [ite_eq_left h1,ih (by omega) hj,ih (by omega) (by omega),show j/4 = b by omega]
      simp (disch := omega) only [ite_eq_left,ite_eq_right]
    · rw [ite_eq_right h1]
      by_cases h2 : 2*2*b+2 ≤ j ∧ j < 2*2*b+2+2
      · rw [ite_eq_left h2,ih (by omega) (by omega),ih (by omega) hj,show j/4 = b by omega]
        simp (disch := omega) only [ite_eq_left,ite_eq_right]
      · rw [ite_eq_right h2,ih (by omega) hj]
        by_cases h3 : j < 4*b <;> simp (disch := omega) only [ite_eq_left,ite_eq_right]

end VG.Proof.MlDsa.Arith
