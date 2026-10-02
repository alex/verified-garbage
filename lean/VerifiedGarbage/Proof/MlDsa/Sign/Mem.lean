import VerifiedGarbage.Proof.MlKem.Mem
import VerifiedGarbage.Spec.MlDsa.Poly

/-!
# ML-DSA: polynomials in memory, for every target

The stored polynomials of `Spec/MlDsa/Poly.lean` (`coeffAt`, `polyAt`,
`natPolyAt`, `hintAt`, `Reduced`, `PolyIs`) depend only on the 1024 bytes of
the polynomial, so they survive writes elsewhere (`…_frame`).
-/

namespace VG.Proof.MlDsa.Sign

open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)
open VG.Proof.MlKem (bytes_frame)

/-- The 1024 bytes of a polynomial at `p`. -/
abbrev pR (p : Addr) : Region := ⟨p, 1024⟩

theorem read_congr₂ {m m' : Mem} {a a' : Addr} {n : Nat}
    (h : ∀ i < n, m' (a' + BitVec.ofNat 64 i) = m (a + BitVec.ofNat 64 i)) :
    m'.read a' n = m.read a n := by
  induction n generalizing a a' with
  | zero => rfl
  | succ n ih =>
    simp only [Mem.read]
    have h0 := h 0 (by omega)
    simp only [BitVec.add_zero] at h0
    rw [h0, ih fun i hi => ?_]
    have := h (i + 1) (by omega)
    rwa [Offset.add_ofNat_succ, Offset.add_ofNat_succ] at this

/-- Coefficients whose bytes are the same. -/
theorem coeffAt_congr₂ {m m' : Mem} {p p' : Addr}
    (h : ∀ k < 1024, m' (p' + BitVec.ofNat 64 k) = m (p + BitVec.ofNat 64 k)) {i : Nat} (hi : i < 256) :
    coeffAt m' p' i = coeffAt m p i := by
  simp only [coeffAt, Mem.readW]
  rw [read_congr₂ fun j hj => ?_]
  rw [BitVec.add_assoc, ← BitVec.ofNat_add, BitVec.add_assoc, ← BitVec.ofNat_add]
  exact h _ (by omega)

theorem polyAt_congr₂ {m m' : Mem} {p p' : Addr}
    (h : ∀ k < 1024, m' (p' + BitVec.ofNat 64 k) = m (p + BitVec.ofNat 64 k)) : polyAt m' p' = polyAt m p := by
  apply Vector.ext
  intro i hi
  simp only [polyAt, Vector.getElem_ofFn]
  rw [coeffAt_congr₂ h hi]

theorem natPolyAt_congr₂ {m m' : Mem} {p p' : Addr}
    (h : ∀ k < 1024, m' (p' + BitVec.ofNat 64 k) = m (p + BitVec.ofNat 64 k)) :
    natPolyAt m' p' = natPolyAt m p := by
  apply Vector.ext
  intro i hi
  simp only [natPolyAt, Vector.getElem_ofFn]
  rw [coeffAt_congr₂ h hi]

theorem reduced_congr₂ {m m' : Mem} {p p' : Addr}
    (h : ∀ k < 1024, m' (p' + BitVec.ofNat 64 k) = m (p + BitVec.ofNat 64 k)) (hr : Reduced m p) :
    Reduced m' p' :=
  fun i hi => by rw [coeffAt_congr₂ h hi]; exact hr i hi

theorem polyIs_congr₂ {m m' : Mem} {p p' : Addr} {f : Poly}
    (h : ∀ k < 1024, m' (p' + BitVec.ofNat 64 k) = m (p + BitVec.ofNat 64 k)) (hf : PolyIs m p f) :
    PolyIs m' p' f :=
  ⟨reduced_congr₂ h hf.1, by rw [polyAt_congr₂ h]; exact hf.2⟩

theorem polyAt_congr {m m' : Mem} {p : Addr}
    (h : ∀ k < 1024, m' (p + BitVec.ofNat 64 k) = m (p + BitVec.ofNat 64 k)) : polyAt m' p = polyAt m p :=
  polyAt_congr₂ h

theorem natPolyAt_congr {m m' : Mem} {p : Addr}
    (h : ∀ k < 1024, m' (p + BitVec.ofNat 64 k) = m (p + BitVec.ofNat 64 k)) : natPolyAt m' p = natPolyAt m p :=
  natPolyAt_congr₂ h

theorem reduced_congr {m m' : Mem} {p : Addr}
    (h : ∀ k < 1024, m' (p + BitVec.ofNat 64 k) = m (p + BitVec.ofNat 64 k)) (hr : Reduced m p) : Reduced m' p :=
  reduced_congr₂ h hr

theorem polyIs_congr {m m' : Mem} {p : Addr} {f : Poly}
    (h : ∀ k < 1024, m' (p + BitVec.ofNat 64 k) = m (p + BitVec.ofNat 64 k)) (hf : PolyIs m p f) : PolyIs m' p f :=
  polyIs_congr₂ h hf

theorem polyAt_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr}
    (hd : ∀ r ∈ rs, (pR p).Disjoint r) : polyAt m' p = polyAt m p :=
  polyAt_congr (bytes_frame hf hd (by decide))

theorem natPolyAt_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr}
    (hd : ∀ r ∈ rs, (pR p).Disjoint r) : natPolyAt m' p = natPolyAt m p :=
  natPolyAt_congr (bytes_frame hf hd (by decide))

theorem reduced_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr}
    (hd : ∀ r ∈ rs, (pR p).Disjoint r) (hr : Reduced m p) : Reduced m' p :=
  reduced_congr (bytes_frame hf hd (by decide)) hr

theorem polyIs_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr} {f : Poly}
    (hd : ∀ r ∈ rs, (pR p).Disjoint r) (h : PolyIs m p f) : PolyIs m' p f :=
  polyIs_congr (bytes_frame hf hd (by decide)) h

/-- A hint of `k` polynomials whose bytes are the same. -/
theorem hintAt_congr {m m' : Mem} {p : Addr} {k : Nat}
    (h : ∀ x < 1024 * k, m' (p + BitVec.ofNat 64 x) = m (p + BitVec.ofNat 64 x)) : hintAt m' p k = hintAt m p k := by
  unfold hintAt
  refine List.map_congr_left fun i hi => ?_
  rw [List.mem_range] at hi
  apply Vector.ext
  intro j hj
  have hj' : j < 256 := hj
  simp only [Vector.getElem_ofFn]
  have e : coeffAt m' p (256 * i + j) = coeffAt m p (256 * i + j) := by
    unfold coeffAt
    refine Mem.readW_congr fun t ht => ?_
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
    exact h (4 * (256 * i + j) + t) (by omega)
  rw [e]

/-- The coefficients `0, …, len - 1` of the `u32`s at `p`, whose bytes are the same. -/
theorem coeffs_congr {m m' : Mem} {p : Addr} {len : Nat}
    (h : ∀ x < 4 * len, m' (p + BitVec.ofNat 64 x) = m (p + BitVec.ofNat 64 x)) :
    (List.range len).map (fun i => (coeffAt m' p i).toNat) = (List.range len).map (fun i => (coeffAt m p i).toNat) := by
  refine List.map_congr_left fun i hi => ?_
  rw [List.mem_range] at hi
  have e : coeffAt m' p i = coeffAt m p i := by
    unfold coeffAt
    refine Mem.readW_congr fun t ht => ?_
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
    exact h (4 * i + t) (by omega)
  rw [e]

theorem bytes_of_bytesAt {m m' : Mem} {p p' : Addr} {len : Nat} (h : bytesAt m' p' len = bytesAt m p len) :
    ∀ k < len, m' (p' + BitVec.ofNat 64 k) = m (p + BitVec.ofNat 64 k) := fun k hk => by
  have := congrArg (fun L => L[k]?) h
  simp only [bytesAt, List.getElem?_map, List.getElem?_range hk, Option.map_some, Option.some.injEq] at this
  exact this

/-- A polynomial whose bytes are those of another. -/
theorem polyIs_of_bytes {m m' : Mem} {p p' : Addr} {f : Poly}
    (h : bytesAt m' p' 1024 = bytesAt m p 1024) (hf : PolyIs m p f) : PolyIs m' p' f :=
  polyIs_congr₂ (bytes_of_bytesAt h) hf

end VG.Proof.MlDsa.Sign
