import VerifiedGarbage.Proof.Sha3.AArch64.Neon.Rotate
import VerifiedGarbage.Proof.Sha3.Spec
import VerifiedGarbage.Proof.Framework.Range

namespace VG.Proof.Sha3.AArch64.Neon
open VG VG.AArch64
open VG.Impl.Sha3.AArch64.Neon.Vector
open VG.Impl.Sha3.AArch64.Sha3.Vector (vreg)
open VG.Proof.MlKem.AArch64 (wp_vop VChg)
open VG.Proof.Sha3 (C)

def Pairs (s : State) (A B : Spec.Sha3.State) : Prop :=
  ∀ i < 25, s.v (vreg i) = ofVDwords A[i]! B[i]!

theorem vreg_inj : ∀ i < 32, ∀ j < 32, vreg i = vreg j ↔ i = j := by decide

theorem pair_xor (a b c d : BitVec 64) :
    ofVDwords a b ^^^ ofVDwords c d = ofVDwords (a ^^^ c) (b ^^^ d) := by
  apply vec64_ext <;> simp only [vdword,BitVec.extractLsb'_xor]
  · change vdword (ofVDwords a b) 0 ^^^ vdword (ofVDwords c d) 0 = vdword (ofVDwords (a ^^^ c) (b ^^^ d)) 0
    rw [vdword_ofVDwords_0,vdword_ofVDwords_0,vdword_ofVDwords_0]
  · change vdword (ofVDwords a b) 1 ^^^ vdword (ofVDwords c d) 1 = vdword (ofVDwords (a ^^^ c) (b ^^^ d)) 1
    rw [vdword_ofVDwords_1,vdword_ofVDwords_1,vdword_ofVDwords_1]

/-- The parity of each column is computed independently for both SHAKE streams. -/
theorem parity_ok {s : State} {A B : Spec.Sha3.State} (hp : Pairs s A B) {x : Nat} (hx : x < 5) :
    WP isa (.block (parity x)) s fun s' => VChg [vreg (25+x)] s s' ∧
      s'.v (vreg (25+x)) = ofVDwords (C A x) (C B x) := by
  have hn (j : Nat) (hj : j < 25) : vreg j ≠ vreg (25+x) := by
    rw [ne_eq,vreg_inj j (by omega) (25+x) (by omega)]; omega
  unfold parity
  refine wp_vop (d := vreg (25+x)) rfl fun s₁ h1 =>
    wp_vop (d := vreg (25+x)) rfl fun s₂ h2 =>
    wp_vop (d := vreg (25+x)) rfl fun s₃ h3 =>
    wp_vop (d := vreg (25+x)) rfl fun s₄ h4 =>
      WP.block_nil_iff.mpr ⟨(((h1.chg.trans h2.chg).trans h3.chg).trans h4.chg).mono
        (by intro r hr; simpa using hr),?_⟩
  rw [h4.v,h3.v,h2.v,h1.v,
    h3.get (vreg (x+20)) (hn _ (by omega)),h2.get (vreg (x+20)) (hn _ (by omega)),
    h1.get (vreg (x+20)) (hn _ (by omega)),h2.get (vreg (x+15)) (hn _ (by omega)),
    h1.get (vreg (x+15)) (hn _ (by omega)),h1.get (vreg (x+10)) (hn _ (by omega)),
    hp x (by omega),hp (x+5) (by omega),hp (x+10) (by omega),hp (x+15) (by omega),hp (x+20) (by omega)]
  simp only [pair_xor,C]
/-- All five column parities are ready before any state lane changes. -/
theorem parityAll_ok {s : State} {A B : Spec.Sha3.State} (hp : Pairs s A B) :
    WP isa (.block ((List.range 5).flatMap parity)) s fun s' =>
      VChg [.v25,.v26,.v27,.v28,.v29] s s' ∧ Pairs s' A B ∧
      ∀ x < 5, s'.v (vreg (25+x)) = ofVDwords (C A x) (C B x) := by
  have hmem : ∀ x < 5, vreg (25+x) ∈ [VReg.v25,.v26,.v27,.v28,.v29] := by decide
  refine wp_range_flatMap (M := isa)
    (fun k s' => VChg [.v25,.v26,.v27,.v28,.v29] s s' ∧ Pairs s' A B ∧
      ∀ x < k, s'.v (vreg (25+x)) = ofVDwords (C A x) (C B x))
    (fun k s' hk ⟨hkeep,hpairs,hcols⟩ => ?_) 5 (Nat.le_refl _) s
    ⟨VChg.refl _ _,hp,fun _ h => False.elim (Nat.not_lt_zero _ h)⟩
  refine WP.mono (parity_ok hpairs hk) fun s'' ⟨hchg,hcol⟩ => ⟨?_,?_,?_⟩
  · exact (hkeep.trans hchg).mono (by
      intro r hr
      rw [List.mem_append,List.mem_singleton] at hr
      rcases hr with h | rfl
      · exact h
      · exact hmem k hk)
  · intro i hi
    rw [hchg.get (vreg i) (by
      simp only [List.mem_singleton]
      rw [vreg_inj i (by omega) (25+k) (by omega)]; omega)]
    exact hpairs i hi
  · intro x hx
    by_cases he : x = k
    · subst x; exact hcol
    · rw [hchg.get (vreg (25+x)) (by
        simp only [List.mem_singleton]
        rw [vreg_inj (25+x) (by omega) (25+k) (by omega)]; omega)]
      exact hcols x (by omega)
end VG.Proof.Sha3.AArch64.Neon
