import VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Neon.PackedTable

namespace VG.Proof.MlDsa.AArch64.Arith.Neon
open VG VG.AArch64
open VG.Impl.MlDsa.AArch64.Arith.Neon
open VG.Proof.MlKem.AArch64 (VChg wp_vop)
open VG.Spec.MlDsa (Zq)

/-- Coefficient index of the lower butterfly operand in a packed group. -/
def lower (len e : Nat) : Nat := e+len*(e/len)

/-- Butterfly lane holding coefficient `r` of a packed group. -/
def lane (len r : Nat) : Nat := len*(r/(2*len))+r%len

def result (len : Nat) (A B : Nat → Zq) (r : Nat) : Zq :=
  if r%(2*len) < len then A (lane len r) else B (lane len r)

set_option linter.unusedSimpArgs false

theorem gather_ok {s : State} (len : Nat) (hlen : len = 1 ∨ len = 2) {F : Nat → Zq}
    (h6 : Coeffs (s.v .v6) F) (h7 : Coeffs (s.v .v7) (fun e => F (4+e))) :
    WP isa (.block (gather len)) s fun s' => VChg [.v0,.v1] s s' ∧
      Coeffs (s'.v .v0) (fun e => F (lower len e)) ∧
      Coeffs (s'.v .v1) (fun e => F (lower len e+len)) := by
  rcases hlen with rfl | rfl
  · change WP isa (.block [.vop (.perm .uzp1 .s4 .v0 .v6 .v7),.vop (.perm .uzp2 .s4 .v1 .v6 .v7)]) s _
    refine wp_vop (d := .v0) rfl fun s₁ h₁ => wp_vop (d := .v1) rfl fun s₂ h₂ =>
      WP.block_nil_iff.mpr ⟨h₁.chg.trans h₂.chg,?_,?_⟩
    · intro e he
      rw [h₂.get .v0,h₁.v,VG.Proof.MlKem.AArch64.vword_uzp1_s4 _ _ he]
      split
      · rw [h6 _ (by omega)]; exact congrArg (fun i => (F i).val) (by simp [lower]; omega)
      · rw [h7 _ (by omega)]; exact congrArg (fun i => (F i).val) (by simp [lower]; omega)
    · intro e he
      rw [h₂.v,h₁.get .v6,h₁.get .v7,VG.Proof.MlKem.AArch64.vword_uzp2_s4 _ _ he]
      split
      · rw [h6 _ (by omega)]; exact congrArg (fun i => (F i).val) (by simp [lower]; omega)
      · rw [h7 _ (by omega)]; exact congrArg (fun i => (F i).val) (by simp [lower]; omega)
  · change WP isa (.block [.vop (.perm .trn1 .d2 .v0 .v6 .v7),.vop (.perm .trn2 .d2 .v1 .v6 .v7)]) s _
    refine wp_vop (d := .v0) rfl fun s₁ h₁ => wp_vop (d := .v1) rfl fun s₂ h₂ =>
      WP.block_nil_iff.mpr ⟨h₁.chg.trans h₂.chg,?_,?_⟩
    · intro e he
      rw [h₂.get .v0,h₁.v,VG.Proof.MlKem.AArch64.vword_trn1_d2 _ _ he]
      split
      · rw [h6 _ (by omega)]; exact congrArg (fun i => (F i).val) (by simp [lower]; omega)
      · rw [h7 _ (by omega)]; exact congrArg (fun i => (F i).val) (by simp [lower]; omega)
    · intro e he
      rw [h₂.v,h₁.get .v6,h₁.get .v7,VG.Proof.MlKem.AArch64.vword_trn2_d2 _ _ he]
      split
      · rw [h6 _ (by omega)]; exact congrArg (fun i => (F i).val) (by simp [lower]; omega)
      · rw [h7 _ (by omega)]; exact congrArg (fun i => (F i).val) (by simp [lower]; omega)

theorem scatter_ok {s : State} (len : Nat) (hlen : len = 1 ∨ len = 2) {A B : Nat → Zq}
    (ha : Coeffs (s.v .v0) A) (hb : Coeffs (s.v .v5) B) :
    WP isa (.block (scatter len)) s fun s' => VChg [.v6,.v7] s s' ∧
      Coeffs (s'.v .v6) (result len A B) ∧
      Coeffs (s'.v .v7) (fun e => result len A B (4+e)) := by
  rcases hlen with rfl | rfl
  · change WP isa (.block [.vop (.perm .zip1 .s4 .v6 .v0 .v5),.vop (.perm .zip2 .s4 .v7 .v0 .v5)]) s _
    refine wp_vop (d := .v6) rfl fun s₁ h₁ => wp_vop (d := .v7) rfl fun s₂ h₂ =>
      WP.block_nil_iff.mpr ⟨h₁.chg.trans h₂.chg,?_,?_⟩
    · intro e he
      rw [h₂.get .v6,h₁.v,VG.Proof.MlKem.AArch64.vword_zip1_s4' _ _ he]
      split <;> rename_i h
      · rw [ha _ (by omega)]; simp [result,lane,Nat.mod_one,h]
      · rw [hb _ (by omega)]; simp [result,lane,Nat.mod_one,h,show ¬ e%2 < 1 by omega]
    · intro e he
      rw [h₂.v,h₁.get .v0,h₁.get .v5,VG.Proof.MlKem.AArch64.vword_zip2_s4 _ _ he]
      split <;> rename_i h
      · rw [ha _ (by omega)]; simp [result,lane,Nat.mod_one,show (4+e)%2 < 1 by omega,show (4+e)/2 = 2+e/2 by omega]
      · rw [hb _ (by omega)]; simp [result,lane,Nat.mod_one,show ¬ (4+e)%2 < 1 by omega,show (4+e)/2 = 2+e/2 by omega]
  · change WP isa (.block [.vop (.perm .trn1 .d2 .v6 .v0 .v5),.vop (.perm .trn2 .d2 .v7 .v0 .v5)]) s _
    refine wp_vop (d := .v6) rfl fun s₁ h₁ => wp_vop (d := .v7) rfl fun s₂ h₂ =>
      WP.block_nil_iff.mpr ⟨h₁.chg.trans h₂.chg,?_,?_⟩
    · intro e he
      rw [h₂.get .v6,h₁.v,VG.Proof.MlKem.AArch64.vword_trn1_d2 _ _ he]
      split <;> rename_i h
      · rw [ha _ (by omega)]; simp [result,lane,Nat.mod_one,show e%4 < 2 by omega,show e/4 = 0 by omega,show e%2 = e by omega]
      · rw [hb _ (by omega)]; simp [result,lane,Nat.mod_one,show ¬ e%4 < 2 by omega,show e/4 = 0 by omega,show e%2 = e-2 by omega]
    · intro e he
      rw [h₂.v,h₁.get .v0,h₁.get .v5,VG.Proof.MlKem.AArch64.vword_trn2_d2 _ _ he]
      split <;> rename_i h
      · rw [ha _ (by omega)]; simp [result,lane,Nat.mod_one,show (4+e)%4 < 2 by omega,show e%4 < 2 by omega,show (4+e)/4 = 1 by omega,show (4+e)%2 = e by omega]
        exact congrArg (fun i => (A i).val) (by omega)
      · rw [hb _ (by omega)]; simp [result,lane,Nat.mod_one,show ¬ (4+e)%4 < 2 by omega,show ¬ e%4 < 2 by omega,show (4+e)/4 = 1 by omega,show 2+(4+e)%2 = e by omega]
end VG.Proof.MlDsa.AArch64.Arith.Neon
