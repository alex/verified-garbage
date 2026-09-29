import VerifiedGarbage.Proof.MlKem.KPke
import VerifiedGarbage.Proof.MlKem.Mem

/-!
# ML-KEM: lemmas the x86 (32-bit) proofs use that do not depend on the target

Untrusted: everything here is checked by Lean.

* `Samp B a`: `SampleNTT(B)` finishes, with `a`, within some bound on its
  iterations; `a` is then unique (`Samp.unique`), and is `sv B`
  (`sv_eq`). Finitely many that each finish within some bound all finish
  within one (`samp_bound`).
* A polynomial whose coefficients are ANDed with `0 - r`, for `r` 1 or 0:
  unchanged or zero (`mask_poly`).
-/

namespace VG.Proof.MlKem

open VG.Spec.MlKem

/-- `SampleNTT(B)` finishes within some bound on its iterations, with `a`. -/
def Samp (B : List Byte) (a : Poly) : Prop := ∃ it, sampleNTT it B = some a

theorem Samp.unique {B : List Byte} {a b : Poly} (h₁ : Samp B a) (h₂ : Samp B b) : a = b := by
  obtain ⟨i, hi⟩ := h₁
  obtain ⟨j, hj⟩ := h₂
  have e₁ := sampleNTT_mono hi (Nat.le_max_left i j)
  have e₂ := sampleNTT_mono hj (Nat.le_max_right i j)
  rw [e₁] at e₂
  exact Option.some.inj e₂

/-- The polynomial `SampleNTT(B)` gives, if it finishes. -/
noncomputable def sv (B : List Byte) : Poly :=
  @dite _ (∃ a, Samp B a) (Classical.propDecidable _) (fun h => Classical.choose h) (fun _ => zero)

theorem sv_eq {B : List Byte} {a : Poly} (h : Samp B a) : sv B = a := by
  unfold sv
  split
  · exact (Classical.choose_spec ‹∃ a, Samp B a›).unique h
  · exact absurd (⟨a, h⟩ : ∃ a, Samp B a) ‹_›

/-- Finitely many samples, within one bound. -/
theorem samp_bound : ∀ (L : List (List Byte × Poly)), (∀ p ∈ L, Samp p.1 p.2) →
    ∃ M, ∀ p ∈ L, sampleNTT M p.1 = some p.2
  | [], _ => ⟨0, fun _ h => absurd h (List.not_mem_nil)⟩
  | p :: L, h => by
    obtain ⟨M, hM⟩ := samp_bound L fun q hq => h q (List.mem_cons_of_mem _ hq)
    obtain ⟨i, hi⟩ := h p (List.mem_cons_self ..)
    refine ⟨max M i, fun q hq => ?_⟩
    rcases List.mem_cons.mp hq with rfl | hq
    · exact sampleNTT_mono hi (Nat.le_max_right _ _)
    · exact sampleNTT_mono (hM q hq) (Nat.le_max_left _ _)

/-- A polynomial with its coefficients ANDed with `0 - r`, for `r` 1 or 0: unchanged, or zero. -/
theorem mask_poly {m m' : Mem} {p : Addr} {r : BitVec 32} (hr : r = 0 ∨ r = 1)
    (h : ∀ i < 256, coeffAt m' p i = coeffAt m p i &&& (0 - r)) (hred : r = 1 → Reduced m p) :
    Reduced m' p ∧ (r = 1 → polyAt m' p = polyAt m p) := by
  rcases hr with rfl | rfl
  · refine ⟨fun i hi => ?_, fun h => absurd h (by decide)⟩
    rw [h i (by rw [n_eq] at hi; exact hi)]
    simp [q_eq]
  · have e : ∀ i < 256, coeffAt m' p i = coeffAt m p i := fun i hi => by
      rw [h i hi, show (0 : BitVec 32) - 1 = BitVec.allOnes 32 by decide, BitVec.and_allOnes]
    refine ⟨fun i hi => ?_, fun _ => ?_⟩
    · rw [e i (by rw [n_eq] at hi; exact hi)]; exact hred rfl i hi
    · apply Vector.ext
      intro i hi
      simp only [polyAt, Vector.getElem_ofFn]
      rw [e i (by rw [n_eq] at hi; exact hi)]

end VG.Proof.MlKem
