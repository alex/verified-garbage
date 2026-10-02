import VerifiedGarbage.Proof.Sha3.AArch64.Neon.SaveRow

namespace VG.Proof.Sha3.AArch64.Neon
open VG VG.AArch64
open VG.Impl.Sha3.AArch64.Neon.Vector
open VG.Impl.Sha3.AArch64.Sha3.Vector (vreg)
open VG.Proof.MlKem.AArch64 (wp_vop VChg)

theorem pair_bic (a b c d : BitVec 64) :
    ofVDwords a b &&& ~~~(ofVDwords c d) = ofVDwords (a &&& ~~~c) (b &&& ~~~d) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [ofVDwords,BitVec.getLsbD_and,BitVec.getLsbD_not,BitVec.getLsbD_append]
  by_cases h : i < 64
  · simp only [h,hi,decide_true,Bool.true_and,ite_true]
  · simp only [h,hi,show i-64 < 64 by omega,decide_true,Bool.true_and,ite_false]

/-- One chi word, with all five row inputs still preserved in temporaries. -/
theorem chiWord_ok {s : State} {x y : Nat} (hx : x < 5) (_hy : y < 5)
    {F G : Nat → BitVec 64}
    (hp : ∀ z < 5, s.v (vreg (25+z)) = ofVDwords (F z) (G z)) :
    WP isa (.block (chiWord x y)) s fun s' => VChg [.v30,vreg (x+5*y)] s s' ∧
      s'.v (vreg (x+5*y)) = ofVDwords
        (F x ^^^ (F ((x+2)%5) &&& ~~~(F ((x+1)%5))))
        (G x ^^^ (G ((x+2)%5) &&& ~~~(G ((x+1)%5)))) := by
  have hn : ∀ z < 5, vreg (25+z) ≠ VReg.v30 := by decide
  unfold chiWord
  refine wp_vop (d := .v30) rfl fun s₁ h1 =>
    wp_vop (d := vreg (x+5*y)) rfl fun s₂ h2 =>
      WP.block_nil_iff.mpr ⟨(h1.chg.trans h2.chg).mono (by intro r hr; simpa using hr),?_⟩
  rw [h2.v,h1.get _ (hn x hx),h1.v,hp x hx,hp ((x+2)%5) (by omega),hp ((x+1)%5) (by omega)]
  change ofVDwords (F x) (G x) ^^^
    (ofVDwords (F ((x+2)%5)) (G ((x+2)%5)) &&& ~~~(ofVDwords (F ((x+1)%5)) (G ((x+1)%5)))) = _
  rw [pair_bic,pair_xor]
end VG.Proof.Sha3.AArch64.Neon
