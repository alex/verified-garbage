import VerifiedGarbage.Proof.MlDsa.KeyGen.Leak
import VerifiedGarbage.Spec.MlDsa.Contract

/-!
# ML-DSA key generation: masked samples, and the leakage as bytes

Untrusted: everything here is checked by Lean. A sampler's result `r` (0 or
1) is ANDed into an accumulator (`acc_and`), and its polynomial with `-r`
(`masked`): kept if the sampler succeeded, zero (reduced, and small) if it
failed. What key generation may leak (`keyGenLeak`) is a list of numbers
less than 256 (`keyGenLeak_lt`), so as bytes it is the same exactly when it
is the same (`map_ofNat_inj`).
-/

namespace VG.Proof.MlDsa.KeyGen

open VG.Spec.MlDsa

/-! ## Masks -/

theorem acc_and {a r : BitVec 32} (ha : a = 0 ∨ a = 1) (hr : r = 0 ∨ r = 1) :
    (a &&& r = 0 ∨ a &&& r = 1) ∧ (a &&& r = 1 ↔ a = 1 ∧ r = 1) := by
  rcases ha with rfl | rfl <;> rcases hr with rfl | rfl <;> decide

/-- The zero polynomial, as the samplers' outputs are when they fail. -/
abbrev zeroI : IPoly := Vector.replicate 256 0

/-- A polynomial masked with the result `r` of the sampler that wrote it. -/
theorem masked {m m' : Mem} {p : Addr} {r : BitVec 32} (hr : r = 0 ∨ r = 1)
    (h : ∀ i < 256, coeffAt m' p i = coeffAt m p i &&& (0 - r)) :
    (r = 1 → (∀ i < 256, coeffAt m' p i = coeffAt m p i) ∧ polyAt m' p = polyAt m p ∧
        (Reduced m p → Reduced m' p)) ∧
      (r = 0 → PolyIs m' p (toRq zeroI)) := by
  rcases hr with rfl | rfl
  · have h' : ∀ i < 256, coeffAt m' p i = 0 := fun i hi => by rw [h i hi]; simp
    refine ⟨fun e => absurd e (by decide), fun _ => ⟨fun i hi => by rw [h' i hi]; decide, Vector.ext fun i hi => ?_⟩⟩
    simp only [polyAt, Vector.getElem_ofFn, h' i hi, toRq, Vector.getElem_map, Vector.getElem_replicate]
    rfl
  · have h' : ∀ i < 256, coeffAt m' p i = coeffAt m p i := fun i hi => by
      rw [h i hi, show (0 : BitVec 32) - 1 = BitVec.allOnes 32 by decide, BitVec.and_allOnes]
    refine ⟨fun _ => ⟨h', Vector.ext fun i hi => ?_, fun hq i hi => by rw [h' i hi]; exact hq i hi⟩,
      fun e => absurd e (by decide)⟩
    simp only [polyAt, Vector.getElem_ofFn, h' i hi]

theorem zeroI_small (η : Nat) : ∀ c ∈ zeroI.toList, -(η : Int) ≤ c ∧ c ≤ η := fun c hc => by
  rw [Vector.mem_toList_iff, Vector.mem_replicate] at hc
  rw [hc.2]; omega

/-! ## The leakage as bytes -/

theorem map_ofNat_inj : ∀ {a b : List Nat}, (∀ x ∈ a, x < 256) → (∀ x ∈ b, x < 256) →
    a.map (BitVec.ofNat 8) = b.map (BitVec.ofNat 8) → a = b
  | [], [], _, _, _ => rfl
  | [], _ :: _, _, _, h => by cases h
  | _ :: _, [], _, _, h => by cases h
  | x :: a, y :: b, ha, hb, h => by
    simp only [List.map_cons, List.cons.injEq] at h
    have hx := ha x (List.mem_cons_self ..)
    have hy := hb y (List.mem_cons_self ..)
    have := congrArg BitVec.toNat h.1
    rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy] at this
    rw [this, map_ofNat_inj (fun z hz => ha z (List.mem_cons_of_mem _ hz))
      (fun z hz => hb z (List.mem_cons_of_mem _ hz)) h.2]

theorem halfByteOk_le (η b : Nat) : halfByteOk η b < 256 := by
  unfold halfByteOk; split <;> decide

theorem keyGenLeak_lt (p : Params) (ξ : List Byte) : ∀ x ∈ keyGenLeak p ξ, x < 256 := by
  intro x hx
  simp only [keyGenLeak, leakBytes, rejBoundedLeak, List.mem_append, List.mem_map, List.mem_flatMap,
    List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with ⟨b, _, rfl⟩ | ⟨_, _, _, _, rfl | rfl⟩
  · exact b.isLt
  all_goals exact halfByteOk_le _ _

theorem keyGenLeak_bytes {p : Params} {ξ₁ ξ₂ : List Byte}
    (h : (keyGenLeak p ξ₁).map (BitVec.ofNat 8) = (keyGenLeak p ξ₂).map (BitVec.ofNat 8)) :
    keyGenLeak p ξ₁ = keyGenLeak p ξ₂ :=
  map_ofNat_inj (keyGenLeak_lt p ξ₁) (keyGenLeak_lt p ξ₂) h

end VG.Proof.MlDsa.KeyGen
