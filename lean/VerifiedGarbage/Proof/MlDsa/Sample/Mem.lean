import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Spec.MlDsa.Poly

/-!
# ML-DSA: polynomials sampled into memory, for every target

The sampling functions store the coefficients of a polynomial one at a time:
`Stored m p L` says that the first `L.length` coefficients at `p` are those of
the list `L` (each as its representative less than `q`), and a polynomial
stored this way in full is `PolyIs` of the vector of the list
(`stored_polyIs`). A polynomial whose every coefficient holds a value is
`PolyIs` of it (`polyIs_of_coeffAt`).
-/

namespace VG.Proof.MlDsa.Sample

open VG.Spec.MlDsa

theorem ifT {α : Sort _} {p : Prop} [Decidable p] (h : p) (a b : α) : (if p then a else b) = a :=
  ite_eq_left_of_eq_true a b (eq_true h)

theorem ifF {α : Sort _} {p : Prop} [Decidable p] (h : ¬ p) (a b : α) : (if p then a else b) = b :=
  ite_eq_right_of_eq_false a b (eq_false h)

/-- The address of coefficient `i` of the polynomial at `p`. -/
abbrev coeffAddr (p : Addr) (i : Nat) : Addr := p + BitVec.ofNat 64 (4 * i)

/-- The 1024 bytes of a polynomial at `p`. -/
abbrev polyR (p : Addr) : Region := ⟨p, 1024⟩

theorem coeffAt_eq (m : Mem) (p : Addr) (i : Nat) : coeffAt m p i = m.readW (coeffAddr p i) 32 := rfl

theorem coeff_contains (p : Addr) {i : Nat} (hi : i < 256) : (polyR p).Contains (coeffAddr p i) 4 :=
  Offset.contains_base p (by omega) (by omega)

theorem coeff_sep (p : Addr) {i j : Nat} (hi : i < 256) (hj : j < 256) (h : i ≠ j) :
    Mem.Sep (coeffAddr p i) 4 (coeffAddr p j) 4 :=
  Offset.sep p (by omega) (by omega) (by omega)

/-- Writing coefficient `j` of the polynomial at `p`. -/
theorem coeffAt_writeW (m : Mem) (p : Addr) {i j : Nat} (hi : i < 256) (hj : j < 256) (v : BitVec 32) :
    coeffAt (m.writeW (coeffAddr p j) v) p i = if j = i then v else coeffAt m p i := by
  split
  · subst j; exact Mem.readW_writeW_self32 m _ v
  · exact Mem.readW_writeW_sep (coeff_sep p hi hj (Ne.symm ‹_›)) (by decide)

/-- The word that represents `x`. -/
abbrev zw (x : Zq) : BitVec 32 := BitVec.ofNat 32 x.val

theorem zw_toNat (x : Zq) : (zw x).toNat = x.val := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.lt_trans x.isLt (by decide))]

/-- The coefficients `L` are stored at `p`. -/
def Stored (m : Mem) (p : Addr) (L : List Zq) : Prop :=
  ∀ k < L.length, coeffAt m p k = zw (L.getD k 0)

theorem stored_nil (m : Mem) (p : Addr) : Stored m p [] := fun _ h => absurd h (Nat.not_lt_zero _)

/-- Storing the next coefficient. -/
theorem stored_snoc {m : Mem} {p : Addr} {L : List Zq} (h : Stored m p L) (hL : L.length < 256) (x : Zq) :
    Stored (m.writeW (coeffAddr p L.length) (zw x)) p (L ++ [x]) := by
  intro k hk
  rw [List.length_append, List.length_singleton] at hk
  rw [coeffAt_writeW _ _ (show k < 256 by omega) hL]
  by_cases e : L.length = k
  · subst e
    simp only [↓reduceIte]
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
    rfl
  · simp only [e, ↓reduceIte]
    rw [h k (by omega), List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
      List.getElem?_append_left (by omega)]

/-- `Fin.ofNat` of the word that represents `x` is `x`. -/
theorem ofNat_zw (x : Zq) : Fin.ofNat q (zw x).toNat = x := by
  rw [zw_toNat]; exact Fin.ext (Nat.mod_eq_of_lt x.isLt)

/-- The polynomial `f` is stored at `p` if each of its coefficients is. -/
theorem polyIs_of_coeffAt {m : Mem} {p : Addr} {f : Poly} (h : ∀ i < n, coeffAt m p i = zw f[i]!) :
    PolyIs m p f := by
  refine ⟨fun i hi => by rw [h i hi, zw_toNat]; exact (f[i]!).isLt, ?_⟩
  apply Vector.ext
  intro i hi
  simp only [polyAt, Vector.getElem_ofFn]
  rw [h i hi, ofNat_zw, getElem!_pos f i hi]

/-- The polynomial of a list of coefficients (0 past its end). -/
abbrev toPoly (L : List Zq) : Poly := Vector.ofFn fun i => L.getD i.val 0

/-- 256 coefficients stored: the polynomial. -/
theorem stored_polyIs {m : Mem} {p : Addr} {L : List Zq} (h : Stored m p L) (hL : L.length = 256) :
    PolyIs m p (toPoly L) :=
  polyIs_of_coeffAt fun i hi => by
    rw [h i (by simp only [n] at hi; omega), getElem!_pos (toPoly L) i hi]
    simp only [toPoly, Vector.getElem_ofFn]

/-- A stored list is unchanged by writes apart from the polynomial. -/
theorem stored_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr}
    (hd : ∀ r ∈ rs, (polyR p).Disjoint r) {L : List Zq} (h : Stored m p L) (hL : L.length ≤ 256) :
    Stored m' p L := fun k hk => by
  rw [coeffAt_eq, hf.readW (coeff_contains p (by omega)) hd (by decide)]
  exact h k hk

end VG.Proof.MlDsa.Sample
