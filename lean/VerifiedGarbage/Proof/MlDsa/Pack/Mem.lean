import VerifiedGarbage.Spec.MlDsa.Poly
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.Offset

/-!
# ML-DSA: polynomials in memory, for the encodings, on every target

The coefficients of the stored representations of `Spec/MlDsa/Poly.lean`
(`coeffAt`, `polyAt`, `natPolyAt`, `PolyIs`), as the encodings read and write
them: the words of a polynomial, their frame, and `PolyIs` from what each word
holds.
-/

namespace VG.Proof.MlDsa.Pack

open VG.Spec.MlDsa

/-- The address of coefficient `i` of the polynomial at `p`. -/
abbrev coeffAddr (p : Addr) (i : Nat) : Addr := p + BitVec.ofNat 64 (4 * i)

theorem coeffAt_eq (m : Mem) (p : Addr) (i : Nat) : coeffAt m p i = m.readW (coeffAddr p i) 32 := rfl

/-- The 1024 bytes of a polynomial at `p`. -/
abbrev polyRegion (p : Addr) : Region := ⟨p, 1024⟩

theorem coeff_contains (p : Addr) {i : Nat} (hi : i < 256) : (polyRegion p).Contains (coeffAddr p i) 4 :=
  Offset.contains_base p (by omega) (by omega)

theorem n_eq : n = 256 := rfl

theorem q_eq : q = 8380417 := rfl

/-- Coefficient `i` of `polyAt`: the stored word modulo `q`. -/
theorem polyAt_getElem (m : Mem) (p : Addr) {i : Nat} (hi : i < n) :
    (polyAt m p)[i] = Fin.ofNat q (coeffAt m p i).toNat := by
  simp only [polyAt, Vector.getElem_ofFn]

theorem natPolyAt_getElem (m : Mem) (p : Addr) {i : Nat} (hi : i < n) :
    (natPolyAt m p)[i] = (coeffAt m p i).toNat := by
  simp only [natPolyAt, Vector.getElem_ofFn]

/-- Coefficient `i` of a reduced polynomial is the stored word. -/
theorem polyAt_val {m : Mem} {p : Addr} (hr : Reduced m p) {i : Nat} (hi : i < n) :
    ((polyAt m p)[i]).val = (coeffAt m p i).toNat := by
  rw [polyAt_getElem m p hi, Fin.val_ofNat, Nat.mod_eq_of_lt (hr i hi)]

/-- `f` is stored at `p` if each of its coefficients is. -/
theorem polyIs_of_toNat {m : Mem} {p : Addr} {f : Poly}
    (h : ∀ i (hi : i < n), (coeffAt m p i).toNat = (f[i]).val) : PolyIs m p f := by
  refine ⟨fun i hi => by rw [h i hi]; exact (f[i]).isLt, Vector.ext fun i hi => ?_⟩
  rw [polyAt_getElem _ _ hi, h i hi]
  exact Fin.ext (Nat.mod_eq_of_lt (f[i]).isLt)

/-- The coefficients of a polynomial, as a list. -/
theorem toList_ofFn {α : Type} (g : Nat → α) :
    (Vector.ofFn (n := n) fun i => g i.val).toList = (List.range 256).map g := by
  refine List.ext_getElem (by rw [Vector.length_toList, List.length_map, List.length_range]) fun i h₁ h₂ => ?_
  simp only [Vector.getElem_toList, Vector.getElem_ofFn, List.getElem_map, List.getElem_range]

theorem natPolyAt_toList (m : Mem) (p : Addr) :
    (natPolyAt m p).toList = (List.range 256).map fun i => (coeffAt m p i).toNat := by
  unfold natPolyAt; exact toList_ofFn fun i => (coeffAt m p i).toNat

/-- A word of a region disjoint from the frame's regions is unchanged. -/
theorem coeffAt_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr}
    (hd : ∀ r ∈ rs, (polyRegion p).Disjoint r) {i : Nat} (hi : i < 256) : coeffAt m' p i = coeffAt m p i :=
  hf.readW (coeff_contains p hi) hd (by decide)

end VG.Proof.MlDsa.Pack
