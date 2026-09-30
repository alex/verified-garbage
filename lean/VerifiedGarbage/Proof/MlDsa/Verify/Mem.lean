import VerifiedGarbage.Proof.MlKem.Mem
import VerifiedGarbage.Spec.MlDsa.Poly

/-!
# ML-DSA: polynomials in memory, for every target

Untrusted: everything here is checked by Lean. The stored polynomials of
`Spec/MlDsa/Poly.lean` (`coeffAt`, `polyAt`, `Reduced`, `PolyIs`,
`natPolyAt`, `hintAt`) are unchanged by writes elsewhere (`…_congr`,
`…_frame`); a hint stored as `k` polynomials gives each of them to
`vg_mldsa_use_hint` (`hintAt_row`).
-/

namespace VG.Proof.MlDsa.Verify

open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

/-- The 1024 bytes of a polynomial at `p`. -/
abbrev polyRegion (p : Addr) : Region := ⟨p, 1024⟩

theorem coeffAt_congr {m m' : Mem} {p : Addr}
    (h : ∀ k < 1024, m' (p + BitVec.ofNat 64 k) = m (p + BitVec.ofNat 64 k)) {i : Nat} (hi : i < n) :
    coeffAt m' p i = coeffAt m p i := by
  refine Mem.readW_congr fun k hk => ?_
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]
  have : n = 256 := rfl
  exact h (4 * i + k) (by omega)

theorem polyAt_congr {m m' : Mem} {p : Addr}
    (h : ∀ k < 1024, m' (p + BitVec.ofNat 64 k) = m (p + BitVec.ofNat 64 k)) :
    polyAt m' p = polyAt m p := by
  apply Vector.ext
  intro i hi
  simp only [polyAt, Vector.getElem_ofFn, coeffAt_congr h hi]

theorem natPolyAt_congr {m m' : Mem} {p : Addr}
    (h : ∀ k < 1024, m' (p + BitVec.ofNat 64 k) = m (p + BitVec.ofNat 64 k)) :
    natPolyAt m' p = natPolyAt m p := by
  apply Vector.ext
  intro i hi
  simp only [natPolyAt, Vector.getElem_ofFn, coeffAt_congr h hi]

theorem reduced_congr {m m' : Mem} {p : Addr}
    (h : ∀ k < 1024, m' (p + BitVec.ofNat 64 k) = m (p + BitVec.ofNat 64 k)) (hr : Reduced m p) :
    Reduced m' p := fun i hi => by rw [coeffAt_congr h hi]; exact hr i hi

theorem polyIs_congr {m m' : Mem} {p : Addr} {f : Poly}
    (h : ∀ k < 1024, m' (p + BitVec.ofNat 64 k) = m (p + BitVec.ofNat 64 k)) (hf : PolyIs m p f) :
    PolyIs m' p f := ⟨reduced_congr h hf.1, (polyAt_congr h).trans hf.2⟩

section
variable {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr}
  (hd : ∀ r ∈ rs, (polyRegion p).Disjoint r)
include hf hd

theorem polyAt_frame : polyAt m' p = polyAt m p :=
  polyAt_congr (Proof.MlKem.bytes_frame hf hd (by decide))

theorem natPolyAt_frame : natPolyAt m' p = natPolyAt m p :=
  natPolyAt_congr (Proof.MlKem.bytes_frame hf hd (by decide))

theorem reduced_frame (hr : Reduced m p) : Reduced m' p :=
  reduced_congr (Proof.MlKem.bytes_frame hf hd (by decide)) hr

theorem polyIs_frame {f : Poly} (h : PolyIs m p f) : PolyIs m' p f :=
  polyIs_congr (Proof.MlKem.bytes_frame hf hd (by decide)) h

end

/-! ## Hints -/

theorem coeffAt_row (m : Mem) (p : Addr) (r j : Nat) :
    coeffAt m (p + BitVec.ofNat 64 (1024 * r)) j = coeffAt m p (256 * r + j) := by
  unfold coeffAt
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]
  congr 3
  omega

/-- Row `r` of a hint stored as `k` polynomials at `p`: the hint polynomial
at `p + 1024r`. -/
theorem hintAt_row {m : Mem} {p : Addr} {k : Nat} {h : List (Vector Bool n)} (hh : HintIs m p k h)
    {r : Nat} (hr : r < k) :
    (hintAt m (p + BitVec.ofNat 64 (1024 * r)) 1).headD (Vector.replicate n false) =
      h.getD r (Vector.replicate n false) := by
  apply Vector.ext
  intro j hj
  simp only [hintAt, List.range_one, List.map_cons, List.map_nil, List.headD_cons, Nat.mul_zero,
    Nat.zero_add, Vector.getElem_ofFn, coeffAt_row, hh.2 r hr j hj]
  rw [getElem!_pos _ j hj]
  cases (h.getD r (Vector.replicate n false))[j] <;> decide

theorem hintIs_congr {m m' : Mem} {p : Addr} {k : Nat} {h : List (Vector Bool n)}
    (hm : ∀ i < 1024 * k, m' (p + BitVec.ofNat 64 i) = m (p + BitVec.ofNat 64 i)) (hh : HintIs m p k h) :
    HintIs m' p k h := by
  refine ⟨hh.1, fun i hi j hj => ?_⟩
  rw [← hh.2 i hi j hj]
  refine Mem.readW_congr fun t ht => ?_
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]
  have : n = 256 := rfl
  exact hm (4 * (256 * i + j) + t) (by omega)

theorem hintIs_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr} {k : Nat}
    (hk : 1024 * k ≤ 2 ^ 64) (hd : ∀ r ∈ rs, (⟨p, 1024 * k⟩ : Region).Disjoint r) {h : List (Vector Bool n)}
    (hh : HintIs m p k h) : HintIs m' p k h :=
  hintIs_congr (Proof.MlKem.bytes_frame hf hd hk) hh

end VG.Proof.MlDsa.Verify
