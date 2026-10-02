import VerifiedGarbage.Proof.Sha3.AArch64.Neon.Rho

namespace VG.Proof.Sha3.AArch64.Neon
open VG VG.AArch64
open VG.Impl.Sha3.AArch64.Neon.Vector
open VG.Impl.Sha3.AArch64.Sha3.Vector (vreg)
open VG.Proof.MlKem.AArch64 (wp_vop VChg)

theorem saveRow_ok {s : State} {y : Nat} (hy : y < 5) :
    WP isa (.block (saveRow y)) s fun s' => VChg [.v25,.v26,.v27,.v28,.v29] s s' ∧
      ∀ x < 5, s'.v (vreg (25+x)) = s.v (vreg (x+5*y)) := by
  have hm : ∀ x < 5, vreg (25+x) ∈ [VReg.v25,.v26,.v27,.v28,.v29] := by decide
  have hs : ∀ i < 25, vreg i ∉ [VReg.v25,.v26,.v27,.v28,.v29] := by decide
  unfold saveRow
  rw [List.map_eq_flatMap]
  refine wp_range_flatMap (M := isa)
    (fun k s' => VChg [.v25,.v26,.v27,.v28,.v29] s s' ∧
      ∀ x < k, s'.v (vreg (25+x)) = s.v (vreg (x+5*y)))
    (fun k s' hk ⟨hchg,hvals⟩ => ?_) 5 (Nat.le_refl _) s
    ⟨VChg.refl _ _,fun _ h => False.elim (Nat.not_lt_zero _ h)⟩
  refine wp_vop (d := vreg (25+k)) rfl fun s'' h => WP.block_nil_iff.mpr ⟨?_,?_⟩
  · exact (hchg.trans h.chg).mono (by
      intro r hr
      rw [List.mem_append,List.mem_singleton] at hr
      rcases hr with hh | rfl
      · exact hh
      · exact hm k hk)
  · intro x hx
    by_cases he : x = k
    · subst x
      rw [h.v,hchg.get _ (hs _ (by omega))]
    · rw [h.get _ (by
        rw [ne_eq,vreg_inj (25+x) (by omega) (25+k) (by omega)]; omega)]
      exact hvals x (by omega)
end VG.Proof.Sha3.AArch64.Neon
