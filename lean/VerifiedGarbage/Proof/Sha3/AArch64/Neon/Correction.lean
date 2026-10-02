import VerifiedGarbage.Proof.Sha3.AArch64.Neon.Column

namespace VG.Proof.Sha3.AArch64.Neon
open VG VG.AArch64
open VG.Impl.Sha3.AArch64.Neon.Vector
open VG.Impl.Sha3.AArch64.Sha3.Vector (vreg)
open VG.Proof.MlKem.AArch64 (wp_vop VChg)
open VG.Proof.Sha3 (C D)
set_option linter.unusedSimpArgs false

/-- Compute and apply a theta correction without disturbing any column parity. -/
theorem correction_ok {s : State} {A B : Spec.Sha3.State} {x : Nat} (hx : x < 5)
    (hc : ∀ c < 5, s.v (vreg (25+c)) = ofVDwords (C A c) (C B c)) :
    WP isa (.block (correction x)) s fun s' =>
      VChg (.v30 :: columnRegs x) s s' ∧
      (∀ c < 5, s'.v (vreg (25+c)) = ofVDwords (C A c) (C B c)) ∧
      ∀ i < 25, s'.v (vreg i) =
        if i%5 = x then s.v (vreg i) ^^^ ofVDwords (D A x) (D B x) else s.v (vreg i) := by
  have h30 (j : Nat) (hj : j < 30) : vreg j ≠ VReg.v30 := by
    change vreg j ≠ vreg 30
    rw [ne_eq,vreg_inj j (by omega) 30 (by decide)]; omega
  unfold correction
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (rol_ok (d := .v30) (n := vreg (25+(x+1)%5))
    (Ne.symm (h30 _ (by omega))) (by decide) (by decide)) fun s₁ ⟨h1,v1⟩ => ?_
  simp only [List.cons_append,List.nil_append]
  refine wp_vop (d := .v30) rfl fun s₂ h2 => ?_
  have v2 : s₂.v .v30 = ofVDwords (D A x) (D B x) := by
    rw [h2.v,h1.get (vreg (25+(x+4)%5)) (by simp only [List.mem_singleton]; exact h30 _ (by omega)),
      hc _ (by omega),v1,hc _ (by omega),vdword_ofVDwords_0,vdword_ofVDwords_1,pair_xor]
    rw [VG.Proof.Sha3.rotateLeft_eq _ (by decide) (by decide),
      VG.Proof.Sha3.rotateLeft_eq _ (by decide) (by decide)]
    simp only [D]; rw [BitVec.xor_comm (C A _),BitVec.xor_comm (C B _)]
  refine WP.mono (column_ok x hx s₂) fun s₃ ⟨h3,_,vals⟩ => ⟨?_,?_,?_⟩
  · exact ((h1.trans h2.chg).trans h3).mono (by
      intro r hr
      simp only [List.mem_append,List.mem_singleton,List.mem_cons,List.not_mem_nil,or_false] at hr ⊢
      rcases hr with (rfl | rfl) | h
      · exact Or.inl rfl
      · exact Or.inl rfl
      · exact Or.inr h)
  · intro c hcc
    have hn : vreg (25+c) ∉ columnRegs x := by
      intro hh
      obtain ⟨y,hy,he⟩ := List.mem_map.mp hh
      rw [List.mem_range] at hy
      have hh := (vreg_inj (x+5*y) (by omega) (25+c) (by omega)).mp he
      omega
    rw [h3.get _ hn,h2.get _ (h30 _ (by omega)),h1.get _ (by
      simp only [List.mem_singleton]; exact h30 _ (by omega))]
    exact hc c hcc
  · intro i hi
    rw [vals i hi,v2,h2.get _ (h30 _ (by omega)),h1.get _ (by
      simp only [List.mem_singleton]; exact h30 _ (by omega))]
end VG.Proof.Sha3.AArch64.Neon
