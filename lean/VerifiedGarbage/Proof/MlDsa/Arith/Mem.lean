import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Spec.MlDsa.Poly
import VerifiedGarbage.Proof.MlDsa.Arith.Zq
import VerifiedGarbage.Proof.Framework.Offset

/-!
# ML-DSA: polynomials in memory, for every target

How the stored representation of `Spec/MlDsa/Poly.lean` (a polynomial as
`[u32; 256]`, `coeffAt`, `polyAt`, `Reduced`, `PolyIs`) changes when a program
writes a coefficient, and how to conclude `PolyIs` from what each word holds.
-/

namespace VG.Proof.MlDsa.Arith

open VG.Spec.MlDsa

/-- The address of coefficient `i` of the polynomial at `p`. -/
abbrev coeffAddr (p : Addr) (i : Nat) : Addr := p + BitVec.ofNat 64 (4 * i)

theorem coeffAt_eq (m : Mem) (p : Addr) (i : Nat) : coeffAt m p i = m.readW (coeffAddr p i) 32 := rfl

/-- The 1024 bytes of a polynomial at `p`. -/
abbrev polyRegion (p : Addr) : Region := ⟨p, 1024⟩

theorem coeff_contains (p : Addr) {i : Nat} (hi : i < n) : (polyRegion p).Contains (coeffAddr p i) 4 := by
  rw [n_eq] at hi; exact Offset.contains_base p (by omega) (by omega)

theorem coeff_sep (p : Addr) {i j : Nat} (hi : i < n) (hj : j < n) (h : i ≠ j) :
    Mem.Sep (coeffAddr p i) 4 (coeffAddr p j) 4 := by
  rw [n_eq] at hi hj; exact Offset.sep p (by omega) (by omega) (by omega)

theorem coeffAddr_add (p : Addr) (j len : Nat) :
    coeffAddr p j + BitVec.ofNat 64 (4 * len) = coeffAddr p (j + len) := by
  rw [coeffAddr, coeffAddr, BitVec.add_assoc, ← BitVec.ofNat_add, Nat.mul_add]

theorem coeffAddr_succ (p : Addr) (j : Nat) : coeffAddr p j + 4 = coeffAddr p (j + 1) :=
  coeffAddr_add p j 1

theorem coeffAt_writeW_self (m : Mem) (p : Addr) (i : Nat) (v : BitVec 32) :
    coeffAt (m.writeW (coeffAddr p i) v) p i = v :=
  Mem.readW_writeW_self32 m _ v

theorem coeffAt_writeW_ne (m : Mem) (p : Addr) {i j : Nat} (hi : i < n) (hj : j < n) (h : i ≠ j)
    (v : BitVec 32) : coeffAt (m.writeW (coeffAddr p j) v) p i = coeffAt m p i :=
  Mem.readW_writeW_sep (coeff_sep p hi hj h) (by decide)

/-- Writing coefficient `j` of the polynomial at `p`. -/
theorem coeffAt_writeW (m : Mem) (p : Addr) {i j : Nat} (hi : i < n) (hj : j < n) (v : BitVec 32) :
    coeffAt (m.writeW (coeffAddr p j) v) p i = if j = i then v else coeffAt m p i := by
  split
  · subst j; exact coeffAt_writeW_self m p i v
  · exact coeffAt_writeW_ne m p hi hj (Ne.symm ‹_›) v

/-- Coefficient `i` of `polyAt`: the stored word modulo `q`. -/
theorem polyAt_get (m : Mem) (p : Addr) {i : Nat} (hi : i < n) :
    (polyAt m p)[i]! = ofNat (coeffAt m p i).toNat := by
  rw [getElem!_eq _ hi]
  simp only [polyAt, Vector.getElem_ofFn]

/-- Coefficient `i` of a reduced polynomial is the stored word. -/
theorem polyAt_val {m : Mem} {p : Addr} (hr : Reduced m p) {i : Nat} (hi : i < n) :
    ((polyAt m p)[i]!).val = (coeffAt m p i).toNat := by
  rw [polyAt_get m p hi, ofNat_of_lt (hr i hi)]

theorem reduced_writeW {m : Mem} {p : Addr} (hr : Reduced m p) {j : Nat} (hj : j < n) {v : BitVec 32}
    (hv : v.toNat < q) : Reduced (m.writeW (coeffAddr p j) v) p := fun i hi => by
  rw [coeffAt_writeW m p hi hj]
  split
  · exact hv
  · exact hr i hi

/-- The word stored for coefficient `i` of `f`. -/
theorem polyIs_toNat {m : Mem} {p : Addr} {f : Poly} (h : PolyIs m p f) {i : Nat} (hi : i < n) :
    (coeffAt m p i).toNat = (f[i]!).val := by
  rw [← h.2, polyAt_val h.1 hi]

/-- `f` is stored at `p` if each of its coefficients is. -/
theorem polyIs_of_toNat {m : Mem} {p : Addr} {f : Poly}
    (h : ∀ i < n, (coeffAt m p i).toNat = (f[i]!).val) : PolyIs m p f := by
  refine ⟨fun i hi => by rw [h i hi]; exact (f[i]!).isLt, ext_getElem! fun i hi => ?_⟩
  rw [polyAt_get _ _ hi, h i hi, ofNat_val]

/-- Writing a coefficient of a stored polynomial: a word whose value is `x`. -/
theorem polyIs_writeW {m : Mem} {p : Addr} {f : Poly} (h : PolyIs m p f) {j : Nat} (hj : j < n) (x : Zq)
    {v : BitVec 32} (hv : v.toNat = x.val) : PolyIs (m.writeW (coeffAddr p j) v) p (f.set! j x) := by
  refine polyIs_of_toNat fun i hi => ?_
  rw [coeffAt_writeW m p hi hj]
  split
  · subst j; rw [getElem!_set!_self _ hi, hv]
  · rw [getElem!_set!_ne _ hi ‹_›, polyIs_toNat h hi]

/-! ## Frames: the polynomial is unchanged by writes elsewhere -/

theorem coeffAt_congr {m m' : Mem} {p : Addr}
    (h : ∀ k < 1024, m' (p + BitVec.ofNat 64 k) = m (p + BitVec.ofNat 64 k)) {i : Nat} (hi : i < n) :
    coeffAt m' p i = coeffAt m p i := by
  rw [n_eq] at hi
  refine Mem.readW_congr fun k hk => ?_
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]
  exact h _ (by omega)

theorem bytes_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr} {len : Nat}
    (hd : ∀ r ∈ rs, (⟨p, len⟩ : Region).Disjoint r) (hlen : len ≤ 2 ^ 64) :
    ∀ k < len, m' (p + BitVec.ofNat 64 k) = m (p + BitVec.ofNat 64 k) :=
  fun _ hk => hf.bytes (R := ⟨p, len⟩) hd hlen hk

theorem coeffAt_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr}
    (hd : ∀ r ∈ rs, (polyRegion p).Disjoint r) {i : Nat} (hi : i < n) : coeffAt m' p i = coeffAt m p i :=
  coeffAt_congr (bytes_frame hf hd (by decide)) hi

theorem polyAt_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr}
    (hd : ∀ r ∈ rs, (polyRegion p).Disjoint r) : polyAt m' p = polyAt m p :=
  ext_getElem! fun i hi => by rw [polyAt_get _ _ hi, polyAt_get _ _ hi, coeffAt_frame hf hd hi]

theorem reduced_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr}
    (hd : ∀ r ∈ rs, (polyRegion p).Disjoint r) (hr : Reduced m p) : Reduced m' p := fun i hi => by
  rw [coeffAt_frame hf hd hi]; exact hr i hi

theorem polyIs_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr} {f : Poly}
    (hd : ∀ r ∈ rs, (polyRegion p).Disjoint r) (h : PolyIs m p f) : PolyIs m' p f :=
  ⟨reduced_frame hf hd h.1, (polyAt_frame hf hd).trans h.2⟩

end VG.Proof.MlDsa.Arith
