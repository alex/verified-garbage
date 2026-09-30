import VerifiedGarbage.Proof.MlDsa.KeyGen.Mono
import VerifiedGarbage.Proof.MlDsa.KeyGen.Poly
import VerifiedGarbage.Proof.MlDsa.KeyGen.Leak

/-!
# ML-DSA key generation: the samplers' results, and masked polynomials

Untrusted: everything here is checked by Lean. Key generation ANDs the
results of the samplers (0 or 1) together (`and01`), and ANDs each sampled
polynomial with the negated result: a polynomial whose sampler succeeded is
kept (`masked_one`), and one whose sampler failed is zero (`masked_zero`),
so reduced and small (`small_zero`). The seeds of the samplers as bytes
(`seedA_eq`, `seedS_eq`).
-/

namespace VG.Proof.MlDsa.KeyGen

open VG.Spec.MlDsa

/-- The coefficients of `x` are in `[-η, η]`. -/
def Small (η : Nat) (x : IPoly) : Prop := ∀ c ∈ x.toList, -(η : Int) ≤ c ∧ c ≤ η

theorem small_zero (η : Nat) : Small η (Vector.replicate 256 0) := fun c hc => by
  rw [Vector.mem_toList_iff, Vector.mem_replicate] at hc
  rw [hc.2]; omega

theorem polyAt_coeff {m m' : Mem} {q : Addr} (h : ∀ i < 256, coeffAt m' q i = coeffAt m q i) :
    polyAt m' q = polyAt m q :=
  Vector.ext fun i hi => by simp only [polyAt, Vector.getElem_ofFn, h i hi]

/-- Kept if the sampler succeeded. -/
theorem masked_one {m m' : Mem} {q : Addr} {r : BitVec 32} (hr : r = 1)
    (h : ∀ i < 256, coeffAt m' q i = if r = 1 then coeffAt m q i else 0) :
    polyAt m' q = polyAt m q ∧ (Reduced m q → Reduced m' q) := by
  have h' : ∀ i < 256, coeffAt m' q i = coeffAt m q i := fun i hi => by rw [h i hi, ifp hr]
  exact ⟨polyAt_coeff h', fun hq i hi => by rw [h' i hi]; exact hq i hi⟩

/-- Zero if it failed. -/
theorem masked_zero {m m' : Mem} {q : Addr} {r : BitVec 32} (hr : r ≠ 1)
    (h : ∀ i < 256, coeffAt m' q i = if r = 1 then coeffAt m q i else 0) :
    PolyIs m' q (toRq (Vector.replicate 256 0)) := by
  have h' : ∀ i < 256, coeffAt m' q i = 0 := fun i hi => by rw [h i hi, ifn hr]
  refine ⟨fun i hi => by rw [h' i hi]; decide, Vector.ext fun i hi => ?_⟩
  simp only [polyAt, Vector.getElem_ofFn, h' i hi, toRq, Vector.getElem_map, Vector.getElem_replicate]
  rfl

theorem outcome_01 {α : Type} {f : Bounds → Option α} {r : BitVec 32} {out : α}
    (h : Outcome f r out) : r = 0 ∨ r = 1 := by
  rcases h with ⟨h, _⟩ | ⟨h, _⟩
  exacts [.inr h, .inl h]

/-- The AND of two results, 0 or 1, in 32 bits, zero-extended. -/
theorem and01 {v : BitVec 64} (hv : v = 0 ∨ v = 1) {r : BitVec 32} (hr : r = 0 ∨ r = 1) :
    BitVec.setWidth 64 (v.setWidth 32 &&& r) = if v = 1 ∧ r = 1 then 1 else 0 := by
  rcases hv with rfl | rfl <;> rcases hr with rfl | rfl <;> decide

/-- The seed of `Â[r, s]`, as bytes. -/
theorem seedA_eq (ρ : List Byte) (r s : Nat) : seedA ρ r s = ρ ++ [BitVec.ofNat 8 s, BitVec.ofNat 8 r] := by
  simp only [seedA, integerToBytes_one, List.append_assoc]; rfl

/-- The seed of entry `r` of `s₁ ‖ s₂`, as bytes. -/
theorem seedS_eq (ρ' : List Byte) {r : Nat} (hr : r < 256) : seedS ρ' r = ρ' ++ [BitVec.ofNat 8 r, 0] := by
  simp only [seedS, integerToBytes_two hr]

end VG.Proof.MlDsa.KeyGen
