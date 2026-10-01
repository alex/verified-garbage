import VerifiedGarbage.Proof.Sha3.AArch64.Sha3.Vector.Round

namespace VG.Proof.Sha3.AArch64.Sha3.Vector

open VG VG.AArch64
open VG.Impl.Sha3.AArch64.Sha3.Vector

theorem rounds_list_ok (rs : List Nat) (hrs : ∀ r ∈ rs, r < 24)
    (s : VG.AArch64.State) (A : Spec.Sha3.State) (hA : Lanes s A) :
    WP isa (.block (rs.flatMap round)) s fun s' =>
      CoreKeep s s' ∧ Lanes s' (rs.foldl Spec.Sha3.rnd A) := by
  induction rs generalizing s A with
  | nil => exact wp_nil ⟨CoreKeep.refl s, hA⟩
  | cons r rs ih =>
    rw [List.flatMap_cons, List.foldl_cons, WP.block_append_iff]
    refine (round_ok r (hrs r (by simp)) s A hA).mono fun s₁ h₁ => ?_
    refine (ih (fun r hr => hrs r (by simp only [List.mem_cons]; exact Or.inr hr))
      s₁ (Spec.Sha3.rnd A r) h₁.2).mono fun s' h₂ => ?_
    exact ⟨h₁.1.trans h₂.1, h₂.2⟩

/-- All 24 rounds preserve scalar ABI fields and compute Keccak-f[1600].
The boundary restores v8–v15 after serializing these result lanes. -/
theorem rounds_ok (s : VG.AArch64.State) (A : Spec.Sha3.State) (hA : Lanes s A) :
    WP isa (.block rounds) s fun s' => CoreKeep s s' ∧ Lanes s' (Spec.Sha3.keccakF A) :=
  rounds_list_ok (List.range 24) (fun _ h => List.mem_range.mp h) s A hA

end VG.Proof.Sha3.AArch64.Sha3.Vector
