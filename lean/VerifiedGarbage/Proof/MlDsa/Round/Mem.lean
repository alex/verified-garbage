import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Spec.MlDsa.Poly

/-!
# ML-DSA: polynomials in memory, for every target

Untrusted: everything here is checked by Lean. How the stored
representation of `Spec/MlDsa/Poly.lean` (a polynomial as `[u32; 256]`:
`coeffAt`, `polyAt`, `natPolyAt`, `hintAt`) changes when a program writes a
coefficient, and how to conclude `PolyIs`, `NatPolyIs` or `HintIs` from what
each word holds.
-/

namespace VG.Proof.MlDsa.Round

open VG.Spec.MlDsa

/-! ## Coefficients -/

theorem n_eq : n = 256 := rfl

/-- The address of coefficient `i` of the polynomial at `p`. -/
abbrev coeffAddr (p : Addr) (i : Nat) : Addr := p + BitVec.ofNat 64 (4 * i)

/-- The 1024 bytes of a polynomial at `p`. -/
abbrev pR (p : Addr) : Region := ⟨p, 1024⟩

theorem coeffAt_eq (m : Mem) (p : Addr) (i : Nat) : coeffAt m p i = m.readW (coeffAddr p i) 32 := rfl

theorem coeff_contains (p : Addr) {i : Nat} (hi : i < n) : (pR p).Contains (coeffAddr p i) 4 := by
  rw [n_eq] at hi; exact Offset.contains_base p (by omega) (by omega)

theorem coeff_sep (p : Addr) {i j : Nat} (hi : i < n) (hj : j < n) (h : i ≠ j) :
    Mem.Sep (coeffAddr p i) 4 (coeffAddr p j) 4 := by
  rw [n_eq] at hi hj; exact Offset.sep p (by omega) (by omega) (by omega)

/-- Writing coefficient `j` of the polynomial at `p`. -/
theorem coeffAt_writeW (m : Mem) (p : Addr) {i j : Nat} (hi : i < n) (hj : j < n) (v : BitVec 32) :
    coeffAt (m.writeW (coeffAddr p j) v) p i = if j = i then v else coeffAt m p i := by
  split
  · subst j; exact Mem.readW_writeW_self32 m _ v
  · exact Mem.readW_writeW_sep (coeff_sep p hi hj (Ne.symm ‹_›)) (by decide)

/-- Writing 4 bytes at `a`, apart from the polynomial at `p`. -/
theorem coeffAt_writeW_disjoint (m : Mem) {p a : Addr} {r : Region} (hd : (pR p).Disjoint r)
    (ha : r.Contains a 4) {i : Nat} (hi : i < n) (v : BitVec 32) :
    coeffAt (m.writeW a v) p i = coeffAt m p i :=
  Mem.readW_writeW_sep (Region.Disjoint.sep hd (coeff_contains p hi) ha) (by decide)

/-- The polynomial at `p` is unchanged by writes to regions disjoint from it. -/
theorem coeffAt_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr}
    (hd : ∀ r ∈ rs, (pR p).Disjoint r) {i : Nat} (hi : i < n) : coeffAt m' p i = coeffAt m p i :=
  hf.readW (coeff_contains p hi) hd (by decide)

/-! ## Polynomials from their coefficients -/

theorem getElem!_eq {α : Type} [Inhabited α] (v : Vector α n) {i : Nat} (hi : i < n) : v[i]! = v[i] :=
  getElem!_pos v i hi

theorem polyAt_get (m : Mem) (p : Addr) {i : Nat} (hi : i < n) :
    (polyAt m p)[i]! = Fin.ofNat q (coeffAt m p i).toNat := by
  rw [getElem!_eq _ hi]
  simp only [polyAt, Vector.getElem_ofFn]

/-- Coefficient `i` of a reduced polynomial is the stored word. -/
theorem polyAt_val {m : Mem} {p : Addr} (hr : Reduced m p) {i : Nat} (hi : i < n) :
    ((polyAt m p)[i]!).val = (coeffAt m p i).toNat := by
  rw [polyAt_get m p hi]
  exact Nat.mod_eq_of_lt (hr i hi)

theorem vector_ext {α : Type} [Inhabited α] {v w : Vector α n} (h : ∀ i < n, v[i]! = w[i]!) : v = w :=
  Vector.ext fun i hi => by have := h i hi; rwa [getElem!_eq _ hi, getElem!_eq _ hi] at this

/-- `f` is stored at `p` if each of its coefficients is. -/
theorem polyIs_of_toNat {m : Mem} {p : Addr} {f : Poly}
    (h : ∀ i < n, (coeffAt m p i).toNat = (f[i]!).val) : PolyIs m p f := by
  refine ⟨fun i hi => by rw [h i hi]; exact (f[i]!).isLt, vector_ext fun i hi => ?_⟩
  rw [polyAt_get _ _ hi, h i hi]
  exact Fin.ext (Nat.mod_eq_of_lt (f[i]!).isLt)

/-- `f` is stored at `p` as its coefficients if each of them is. -/
theorem natPolyIs_of_toNat {m : Mem} {p : Addr} {f : Vector Nat n}
    (h : ∀ i < n, (coeffAt m p i).toNat = f[i]!) : NatPolyIs m p f :=
  vector_ext fun i hi => by
    rw [getElem!_eq _ hi, ← h i hi]
    simp only [natPolyAt, Vector.getElem_ofFn]

theorem map_get {α β : Type} [Inhabited α] [Inhabited β] (v : Vector α n) (f : α → β) {i : Nat} (hi : i < n) :
    (v.map f)[i]! = f v[i]! := by
  rw [getElem!_eq _ hi, getElem!_eq _ hi, Vector.getElem_map]

theorem zipWith_get {α β γ : Type} [Inhabited α] [Inhabited β] [Inhabited γ] (v : Vector α n)
    (w : Vector β n) (f : α → β → γ) {i : Nat} (hi : i < n) :
    (Vector.zipWith f v w)[i]! = f v[i]! w[i]! := by
  rw [getElem!_eq _ hi, getElem!_eq _ hi, getElem!_eq _ hi, Vector.getElem_zipWith]

/-! ## Hints -/

/-- Coefficient `j` of the hint polynomial at `p`: whether its word is not 0. -/
theorem hintAt_get (m : Mem) (p : Addr) {j : Nat} (hj : j < n) :
    ((hintAt m p 1).headD (Vector.replicate n false))[j]! = decide (coeffAt m p j ≠ 0) := by
  rw [getElem!_eq _ hj]
  simp [hintAt]

/-- A hint polynomial is stored at `p` if each of its coefficients is. -/
theorem hintIs_of_toNat {m : Mem} {p : Addr} {h : Vector Bool n}
    (hc : ∀ j < n, coeffAt m p j = h[j]!.toNat) : HintIs m p 1 [h] := by
  refine ⟨rfl, fun i hi j hj => ?_⟩
  obtain rfl : i = 0 := by omega
  simpa using hc j hj

/-- The number of 1s among coefficients `lo` to 255 of a hint polynomial. -/
def onesFrom (h : Vector Bool n) (lo : Nat) : Nat := ((List.range' lo (n - lo)).filter fun j => h[j]!).length

theorem onesFrom_step (h : Vector Bool n) {lo : Nat} (hlo : lo < n) :
    onesFrom h lo = h[lo]!.toNat + onesFrom h (lo + 1) := by
  unfold onesFrom
  rw [show n - lo = (n - (lo + 1)) + 1 by omega, List.range'_succ, List.filter_cons]
  cases h[lo]! <;> simp [Nat.add_comm]

theorem onesFrom_n (h : Vector Bool n) : onesFrom h n = 0 := by simp [onesFrom]

theorem hintOnes_single (h : Vector Bool n) : hintOnes [h] = onesFrom h 0 := by
  have e : h.toList = (List.range' 0 n).map fun j => h[j]! := by
    refine List.ext_getElem (by simp) fun j h₁ h₂ => ?_
    simp only [Vector.getElem_toList, List.getElem_map, List.getElem_range', Nat.zero_add, Nat.one_mul]
    simp only [Vector.length_toList] at h₁
    exact (getElem!_eq h h₁).symm
  simp only [hintOnes, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero, onesFrom, e,
    List.filter_map, List.length_map, Nat.sub_zero]
  rfl

/-! ## The memory of zeros -/

theorem read_zero (a : Addr) : ∀ n, Mem.read (fun _ => 0) a n = 0
  | 0 => rfl
  | n + 1 => by
    rw [Mem.read, read_zero (a + 1) n]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_append]
    have (w : Nat) : (0 : BitVec w).toNat = 0 := BitVec.toNat_zero
    rw [this, this, this]
    rfl

theorem reduced_zero (p : Addr) : Reduced (fun _ => 0) p := fun _ _ => by
  simp only [coeffAt, Mem.readW, read_zero]
  decide

end VG.Proof.MlDsa.Round
