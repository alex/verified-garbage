import VerifiedGarbage.Proof.Argon2.Spec

/-! # Gathering and scattering Argon2 rows and columns -/

namespace VG.Proof.Argon2

open VG.Spec.Argon2

/-- Write selected words of a sixteen-word vector back to the block. -/
def scatter (index : Fin 16 → Fin 128) (xs : List (Fin 16))
    (b : Block) (v : Vector Word 16) : Block :=
  xs.foldl (fun b j => b.set (index j) v[j]) b

theorem scatter_preserves (index : Fin 16 → Fin 128) (hi : Function.Injective index)
    (xs : List (Fin 16)) (b : Block) (v : Vector Word 16) (j : Fin 16)
    (h : b[index j] = v[j]) : (scatter index xs b v)[index j] = v[j] := by
  induction xs generalizing b with
  | nil => exact h
  | cons a xs ih =>
    apply ih
    by_cases ha : a = j
    · subst a
      simp only [Fin.getElem_fin, Vector.getElem_set_self]
    · have hn : (index a).val ≠ (index j).val := fun he => ha (hi (Fin.ext he))
      simpa only [Fin.getElem_fin, Vector.getElem_set, hn, ite_false] using h

theorem scatter_at (index : Fin 16 → Fin 128) (hi : Function.Injective index)
    (xs : List (Fin 16)) (b : Block) (v : Vector Word 16) (j : Fin 16)
    (hj : j ∈ xs) : (scatter index xs b v)[index j] = v[j] := by
  induction xs generalizing b with
  | nil => simp only [List.not_mem_nil] at hj
  | cons a xs ih =>
    rcases List.mem_cons.mp hj with h | h
    · subst a
      apply scatter_preserves index hi xs (b.set (index j) v[j])
      simp only [Fin.getElem_fin, Vector.getElem_set_self]
    · exact ih _ h

theorem scatter_outside (index : Fin 16 → Fin 128) (xs : List (Fin 16))
    (b : Block) (v : Vector Word 16) (k : Fin 128)
    (hk : ∀ j ∈ xs, index j ≠ k) : (scatter index xs b v)[k] = b[k] := by
  induction xs generalizing b with
  | nil => rfl
  | cons a xs ih =>
    rw [show scatter index (a :: xs) b v = scatter index xs (b.set (index a) v[a]) v from rfl,
      ih _ (fun j hj => hk j (List.mem_cons_of_mem _ hj))]
    have hn : (index a).val ≠ k.val := fun he => hk a (by simp) (Fin.ext he)
    simp only [Fin.getElem_fin, Vector.getElem_set, hn, ite_false]

/-- A vector matching all selected words and all untouched words is the scatter. -/
theorem eq_scatter (index : Fin 16 → Fin 128) (hi : Function.Injective index)
    (b t : Block) (v : Vector Word 16) (hg : gather index t = v)
    (ho : ∀ k : Fin 128, (∀ j, index j ≠ k) → t[k] = b[k]) :
    t = scatter index (List.finRange 16) b v := by
  apply Vector.ext
  intro k hk
  by_cases h : ∃ j, index j = ⟨k, hk⟩
  · obtain ⟨j, hj⟩ := h
    have he := congrArg (fun x : Vector Word 16 => x[j]) hg
    rw [gather_get] at he
    have hs := scatter_at index hi (List.finRange 16) b v j (List.mem_finRange j)
    simpa only [hj, Fin.getElem_fin] using he.trans hs.symm
  · have hn : ∀ j, index j ≠ ⟨k, hk⟩ := fun j hj => h ⟨j, hj⟩
    exact (ho ⟨k, hk⟩ hn).trans
      (scatter_outside index (List.finRange 16) b v ⟨k, hk⟩ (fun j _ => hn j)).symm

theorem rowIndex_injective (r : Fin 8) : Function.Injective (rowIndex r) := by
  intro a b h
  have := congrArg Fin.val h
  apply Fin.ext
  simp only [rowIndex] at this
  omega

theorem colIndex_injective (c : Fin 8) : Function.Injective (colIndex c) := by
  intro a b h
  have := congrArg Fin.val h
  apply Fin.ext
  simp only [colIndex] at this
  omega

end VG.Proof.Argon2
