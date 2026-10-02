import VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Neon.Vec

namespace VG.Proof.MlDsa.AArch64.Arith.Neon
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (VChg Lanes wp_vop lanes_add lanes_sub)
open VG.Impl.MlDsa.AArch64.Arith.Neon
open VG.Proof.MlDsa.Arith
open VG.Spec.MlDsa (q)

structure VConsts (s : State) : Prop where
  q : s.v .v16 = ofVWords (BitVec.ofNat 32 q) (BitVec.ofNat 32 q)
    (BitVec.ofNat 32 q) (BitVec.ofNat 32 q)
  qi : s.v .v17 = ofVWords (BitVec.ofNat 32 montQInv) (BitVec.ofNat 32 montQInv)
    (BitVec.ofNat 32 montQInv) (BitVec.ofNat 32 montQInv)

theorem VConsts.chg {s s' : State} (hc : VConsts s) {rs : List VReg} (h : VChg rs s s')
    (h16 : VReg.v16 ∉ rs := by decide) (h17 : VReg.v17 ∉ rs := by decide) : VConsts s' :=
  ⟨by rw [h.get _ h16]; exact hc.q, by rw [h.get _ h17]; exact hc.qi⟩

theorem VConsts.lanes_q {s : State} (hc : VConsts s) : Lanes (s.v .v16) fun _ => VG.Spec.MlDsa.q := by
  rw [hc.q]
  exact VG.Proof.MlKem.AArch64.lanes_dup.congr fun _ _ => by decide

section
variable {rest : List Instr} {s : State} {Q : State → Prop}

theorem mont_lanes {d z : VReg}
    (hd : d ∉ [VReg.v2,.v3,.v4]) (hz : z ∉ [VReg.v2,.v3,.v4]) (hc : VConsts s)
    {A Z : Nat → Nat} (ha : Lanes (s.v d) A) (hzv : Lanes (s.v z) Z)
    (hzlt : ∀ e < 4, Z e < q)
    (k : ∀ s', VChg [.v2,.v3,.v4,d] s s' → Lanes (s'.v d) (fun e => mont (A e * Z e)) →
      WP isa (.block rest) s' Q) : WP isa (.block (Impl.MlDsa.AArch64.Arith.Neon.mont d z ++ rest)) s Q := by
  refine mont_ok hd hz hc.q hc.qi fun s' h hval => k s' h ?_
  intro e he
  rw [hval, vword_ofVWords _ _ _ _ he]
  have hm (i : Nat) (hi : i < 4) :
      (redc (product (vword (s.v d) i) (vword (s.v z) i))).toNat = mont (A i * Z i) := by
    rw [mont_word_nat _ _ (by rw [hzv i hi]; exact hzlt i hi), ha i hi, hzv i hi]
  rcases (show e = 0 ∨ e = 1 ∨ e = 2 ∨ e = 3 by omega) with rfl | rfl | rfl | rfl <;>
    exact hm _ (by decide)

theorem bfly_ok (hc : VConsts s) {A B Z : Nat → Nat}
    (ha : Lanes (s.v .v0) A) (hb : Lanes (s.v .v1) B) (hz : Lanes (s.v .v18) Z)
    (halt : ∀ e < 4, A e < q) (hzlt : ∀ e < 4, Z e < q)
    (k : ∀ s', VChg [.v0,.v1,.v2,.v3,.v4,.v5] s s' →
      Lanes (s'.v .v0) (fun e => (A e + mont (B e*Z e)%q)%q) →
      Lanes (s'.v .v5) (fun e => (A e + q - mont (B e*Z e)%q)%q) →
      WP isa (.block rest) s' Q) : WP isa (.block (bfly ++ rest)) s Q := by
  simp only [bfly, List.append_assoc, List.cons_append]
  have hm : ∀ e < 4, mont (B e*Z e) < 2*q := fun e he =>
    mont_lt (by simpa only [Nat.mul_comm] using Nat.mul_lt_mul'' (hb.lt he) (hzlt e he))
  refine mont_lanes (by decide) (by decide) hc hb hz hzlt fun s₁ h₁ l₁ => ?_
  refine csub_ok (by decide) (hc.chg h₁).lanes_q l₁ hm fun s₂ h₂ l₂ => ?_
  have c₂ := hc.chg (h₁.trans h₂)
  have a₂ : Lanes (s₂.v .v0) A := by rw [h₂.get .v0, h₁.get .v0]; exact ha
  have tlt : ∀ e, mont (B e*Z e)%q < q := fun e => Nat.mod_lt _ (by decide)
  refine wp_vop (d := .v5) rfl fun s₃ h₃ => wp_vop (d := .v0) rfl fun s₄ h₄ => ?_
  have t₃ : Lanes (s₃.v .v1) (fun e => mont (B e*Z e)%q) := by rw [h₃.get .v1]; exact l₂
  have a₃5 : Lanes (s₃.v .v5) A := by rw [h₃.v]; exact a₂
  have a₃ : Lanes (s₃.v .v0) A := by rw [h₃.get .v0]; exact a₂
  have sum : Lanes (s₄.v .v0) (fun e => A e + mont (B e*Z e)%q) := by
    rw [h₄.v]
    exact (lanes_add a₃ t₃).congr fun e he => Nat.mod_eq_of_lt (by
      have ha' := halt e he; have ht' := tlt e; rw [q_eq] at ha' ht' ⊢; omega)
  refine csub_ok (by decide) (c₂.chg (h₃.chg.trans h₄.chg)).lanes_q sum
    (fun e he => by have := halt e he; have := tlt e; omega) fun s₅ h₅ l₅ => ?_
  refine wp_vop (d := .v5) rfl fun s₆ h₆ => wp_vop (d := .v5) rfl fun s₇ h₇ => ?_
  have a₅ : Lanes (s₅.v .v5) A := by rw [h₅.get .v5, h₄.get .v5]; exact a₃5
  have c₅ := c₂.chg ((h₃.chg.trans h₄.chg).trans h₅)
  have a₆ : Lanes (s₆.v .v5) (fun e => A e + q) := by
    rw [h₆.v]
    exact (lanes_add a₅ c₅.lanes_q).congr fun e he => Nat.mod_eq_of_lt (by
      have := halt e he; change A e < 8380417 at this; change A e + 8380417 < 2^32; omega)
  have t₆ : Lanes (s₆.v .v1) (fun e => mont (B e*Z e)%q) := by
    rw [h₆.get .v1, h₅.get .v1, h₄.get .v1, h₃.get .v1]; exact l₂
  have diff : Lanes (s₇.v .v5) (fun e => A e + q - mont (B e*Z e)%q) := by
    rw [h₇.v]
    exact (lanes_sub a₆ t₆).congr fun e he => by
      have := halt e he; have := tlt e; rw [q_eq] at *; omega
  refine csub_ok (by decide) (c₅.chg (h₆.chg.trans h₇.chg)).lanes_q diff
    (fun e he => by have := halt e he; have := tlt e; omega) fun s₈ h₈ l₈ => k s₈
      (((((((h₁.trans h₂).trans h₃.chg).trans h₄.chg).trans h₅).trans h₆.chg).trans h₇.chg).trans h₈).mono ?_ l₈
  rw [h₈.get .v0, h₇.get .v0, h₆.get .v0]; exact l₅

theorem bflyInv_ok (hc : VConsts s) {A B Z : Nat → Nat}
    (ha : Lanes (s.v .v0) A) (hb : Lanes (s.v .v1) B) (hz : Lanes (s.v .v18) Z)
    (halt : ∀ e < 4, A e < q) (hblt : ∀ e < 4, B e < q) (hzlt : ∀ e < 4, Z e < q)
    (k : ∀ s', VChg [.v0,.v2,.v3,.v4,.v5] s s' →
      Lanes (s'.v .v0) (fun e => (A e + B e)%q) →
      Lanes (s'.v .v5) (fun e => mont ((A e + q - B e)*Z e)%q) →
      WP isa (.block rest) s' Q) : WP isa (.block (bflyInv ++ rest)) s Q := by
  simp only [bflyInv, List.append_assoc, List.cons_append]
  refine wp_vop (d := .v5) rfl fun s₁ h₁ => wp_vop (d := .v5) rfl fun s₂ h₂ => ?_
  have a₁ : Lanes (s₁.v .v5) (fun e => A e + q) := by
    rw [h₁.v]
    exact (lanes_add ha hc.lanes_q).congr fun e he => Nat.mod_eq_of_lt (by
      have ha' := halt e he; rw [q_eq] at ha' ⊢; omega)
  have b₁ : Lanes (s₁.v .v1) B := by rw [h₁.get .v1]; exact hb
  have diff : Lanes (s₂.v .v5) (fun e => A e + q - B e) := by
    rw [h₂.v]
    exact (lanes_sub a₁ b₁).congr fun e he => by
      have ha' := halt e he; have hb' := hblt e he; rw [q_eq] at ha' hb' ⊢; omega
  have c₂ := hc.chg (h₁.chg.trans h₂.chg)
  refine wp_vop (d := .v0) rfl fun s₃ h₃ => ?_
  have sum : Lanes (s₃.v .v0) (fun e => A e + B e) := by
    rw [h₃.v]
    exact (lanes_add (by rw [h₂.get .v0, h₁.get .v0]; exact ha)
      (by rw [h₂.get .v1, h₁.get .v1]; exact hb)).congr fun e he => Nat.mod_eq_of_lt (by
        have ha' := halt e he; have hb' := hblt e he; rw [q_eq] at ha' hb'; omega)
  refine csub_ok (by decide) (c₂.chg h₃.chg).lanes_q sum
    (fun e he => by have := halt e he; have := hblt e he; omega) fun s₄ h₄ l₄ => ?_
  have c₄ := c₂.chg (h₃.chg.trans h₄)
  have diff₄ : Lanes (s₄.v .v5) (fun e => A e + q - B e) := by
    rw [h₄.get .v5, h₃.get .v5]; exact diff
  have z₄ : Lanes (s₄.v .v18) Z := by
    rw [h₄.get .v18, h₃.get .v18, h₂.get .v18, h₁.get .v18]; exact hz
  refine mont_lanes (by decide) (by decide) c₄ diff₄ z₄ hzlt fun s₅ h₅ l₅ => ?_
  refine csub_ok (by decide) (c₄.chg h₅).lanes_q l₅
    (fun e he => mont_lt (by
      simpa only [Nat.mul_comm] using Nat.mul_lt_mul'' (diff₄.lt he) (hzlt e he)))
    fun s₆ h₆ l₆ => k s₆ (((((h₁.chg.trans h₂.chg).trans h₃.chg).trans h₄).trans h₅).trans h₆).mono ?_ l₆
  rw [h₆.get .v0, h₅.get .v0]; exact l₄

end
end VG.Proof.MlDsa.AArch64.Arith.Neon
