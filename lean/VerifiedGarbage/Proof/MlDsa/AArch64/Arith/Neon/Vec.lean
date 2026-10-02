import VerifiedGarbage.Impl.MlDsa.AArch64.Arith.Neon.Vec
import VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Neon.Word
import VerifiedGarbage.Proof.MlKem.AArch64.Vec
import VerifiedGarbage.Proof.Framework.AArch64.Simd64

namespace VG.Proof.MlDsa.AArch64.Arith.Neon
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (VChg VUpd Lanes wp_vop lanes_sub lanes_umin)
open VG.Impl.MlDsa.AArch64.Arith.Neon
open VG.Proof.MlDsa.Arith
open VG.Spec.MlDsa (q)

set_option linter.unusedSimpArgs false

/-- Unzip the low or high halves of four widening products. -/
theorem unzip_wide (hi : Bool) (a b c d : BitVec 64) :
    VPermOp.eval (if hi then .uzp2 else .uzp1) .s4 (ofVDwords a b) (ofVDwords c d) =
      ofVWords (a.extractLsb' (if hi then 32 else 0) 32)
        (b.extractLsb' (if hi then 32 else 0) 32)
        (c.extractLsb' (if hi then 32 else 0) 32)
        (d.extractLsb' (if hi then 32 else 0) 32) := by
  apply vec_ext
  intro e he
  rw [vword_ofVWords _ _ _ _ he]
  rcases (show e = 0 ∨ e = 1 ∨ e = 2 ∨ e = 3 by omega) with rfl | rfl | rfl | rfl <;>
    cases hi <;> ext i hi <;>
    simp +arith [VPermOp.eval, VArr.ofLanes, VArr.lanes, vword, ofVDwords,
      ofVWords, BitVec.getElem_extractLsb', BitVec.getLsbD_append, hi]
  all_goals (repeat rw [BitVec.getLsbD_append])
  all_goals simp +arith [BitVec.getLsbD_extractLsb', BitVec.getLsbD_append, hi]
  all_goals rw [BitVec.getLsbD_append]
  all_goals simp +arith [hi]
  all_goals (intro h; omega)

/-- Pointwise operations on a concrete four-word vector. -/
theorem map2_words (f : (w : Nat) → BitVec w → BitVec w → BitVec w)
    (a b c d e f' g h : BitVec 32) :
    VArr.s4.map2 f (ofVWords a b c d) (ofVWords e f' g h) =
      ofVWords (f 32 a e) (f 32 b f') (f 32 c g) (f 32 d h) := by
  apply vec_ext
  intro i hi
  rw [vword_map2 _ _ _ hi, vword_ofVWords _ _ _ _ hi,
    vword_ofVWords _ _ _ _ hi, vword_ofVWords _ _ _ _ hi]
  rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 by omega) with rfl | rfl | rfl | rfl <;> rfl

section
variable {rest : List Instr} {s : State} {Q : State → Prop}

theorem csub_ok {d t : VReg} (hdt : d ≠ t := by decide)
    (hq : Lanes (s.v .v16) fun _ => q) {f : Nat → Nat}
    (hf : Lanes (s.v d) f) (hlt : ∀ e < 4, f e < 2*q)
    (k : ∀ s', VChg [t,d] s s' → Lanes (s'.v d) (fun e => f e % q) →
      WP isa (.block rest) s' Q) :
    WP isa (.block (csub d t ++ rest)) s Q := by
  refine wp_vop (d := t) rfl fun s₁ h₁ => wp_vop (d := d) rfl fun s₂ h₂ =>
    k s₂ (h₁.chg.trans h₂.chg) ?_
  have l₁ := lanes_sub hf hq
  rw [← h₁.v] at l₁
  rw [h₂.v]
  refine (lanes_umin (by rw [h₁.get d hdt]; exact hf) l₁).congr fun e he => ?_
  have := hlt e he
  change f e < 2*8380417 at this
  change min (f e) ((2^32 - 8380417 + f e) % 2^32) = f e % 8380417
  omega

/-- Seven instructions perform REDC on four independent lanes. -/
theorem mont_ok {d z : VReg}
    (hd : d ∉ [VReg.v2, .v3, .v4]) (hz : z ∉ [VReg.v2, .v3, .v4])
    (hq : s.v .v16 = ofVWords (BitVec.ofNat 32 q) (BitVec.ofNat 32 q)
      (BitVec.ofNat 32 q) (BitVec.ofNat 32 q))
    (hqi : s.v .v17 = ofVWords (BitVec.ofNat 32 montQInv) (BitVec.ofNat 32 montQInv)
      (BitVec.ofNat 32 montQInv) (BitVec.ofNat 32 montQInv))
    (k : ∀ s', VChg [.v2,.v3,.v4,d] s s' →
      s'.v d = ofVWords (redc (product (vword (s.v d) 0) (vword (s.v z) 0)))
        (redc (product (vword (s.v d) 1) (vword (s.v z) 1)))
        (redc (product (vword (s.v d) 2) (vword (s.v z) 2)))
        (redc (product (vword (s.v d) 3) (vword (s.v z) 3))) →
      WP isa (.block rest) s' Q) : WP isa (.block (mont d z ++ rest)) s Q := by
  have hd2 : d ≠ .v2 := fun h => hd (by simp [h])
  have hd3 : d ≠ .v3 := fun h => hd (by simp [h])
  have hd4 : d ≠ .v4 := fun h => hd (by simp [h])
  have hz2 : z ≠ .v2 := fun h => hz (by simp [h])
  have hz3 : z ≠ .v3 := fun h => hz (by simp [h])
  have hz4 : z ≠ .v4 := fun h => hz (by simp [h])
  have eq_q : (BitVec.ofNat 32 q).setWidth 64 = BitVec.ofNat 64 q := by decide
  let p := fun e => product (vword (s.v d) e) (vword (s.v z) e)
  refine wp_vop (d := .v2) rfl fun s₁ h₁ => ?_
  have a₁ : s₁.v .v2 = ofVDwords (p 0) (p 1) := h₁.v
  refine wp_vop (d := .v3) rfl fun s₂ h₂ => ?_
  have a₂ : s₂.v .v3 = ofVDwords (p 2) (p 3) := by
    rw [h₂.v, h₁.get d hd2, h₁.get z hz2]
    rfl
  refine wp_vop (d := .v4) rfl fun s₃ h₃ => ?_
  have a₃ : s₃.v .v4 = ofVWords ((p 0).extractLsb' 0 32) ((p 1).extractLsb' 0 32)
      ((p 2).extractLsb' 0 32) ((p 3).extractLsb' 0 32) := by
    rw [h₃.v, h₂.get .v2, a₁, a₂]; exact unzip_wide false _ _ _ _
  refine wp_vop (d := .v4) rfl fun s₄ h₄ => ?_
  have a₄ : s₄.v .v4 = ofVWords (multiplier (p 0)) (multiplier (p 1))
      (multiplier (p 2)) (multiplier (p 3)) := by
    rw [h₄.v, a₃, h₃.get .v17, h₂.get .v17, h₁.get .v17, hqi, map2_words]
    rfl
  refine wp_vop (d := .v2) rfl fun s₅ h₅ => ?_
  have a₅ : s₅.v .v2 = ofVDwords
      (p 0 + (multiplier (p 0)).setWidth 64 * BitVec.ofNat 64 q)
      (p 1 + (multiplier (p 1)).setWidth 64 * BitVec.ofNat 64 q) := by
    rw [h₅.v, h₄.get .v2, h₃.get .v2, h₂.get .v2, a₁, a₄,
      h₄.get .v16, h₃.get .v16, h₂.get .v16, h₁.get .v16, hq]
    simp only [ite_true, ite_false, Bool.false_eq_true, Nat.zero_add, Nat.add_zero, Nat.reduceAdd, vdword_ofVDwords_0, vdword_ofVDwords_1, vword_ofVWords_0,
      vword_ofVWords_1, eq_q]
  refine wp_vop (d := .v3) rfl fun s₆ h₆ => ?_
  have a₆ : s₆.v .v3 = ofVDwords
      (p 2 + (multiplier (p 2)).setWidth 64 * BitVec.ofNat 64 q)
      (p 3 + (multiplier (p 3)).setWidth 64 * BitVec.ofNat 64 q) := by
    rw [h₆.v, h₅.get .v3, h₄.get .v3, h₃.get .v3, a₂, h₅.get .v4, a₄,
      h₅.get .v16, h₄.get .v16, h₃.get .v16, h₂.get .v16, h₁.get .v16, hq]
    simp only [ite_true, ite_false, Bool.false_eq_true, Nat.zero_add, Nat.add_zero, Nat.reduceAdd, vdword_ofVDwords_0, vdword_ofVDwords_1, vword_ofVWords_2,
      vword_ofVWords_3, eq_q]
  refine wp_vop (d := d) rfl fun s₇ h₇ => k s₇
    (VChg.mono (rs' := [.v2,.v3,.v4,d])
      ((((((h₁.chg.trans h₂.chg).trans h₃.chg).trans h₄.chg).trans h₅.chg).trans h₆.chg).trans h₇.chg)
      (by
        intro r hr
        simp only [List.mem_append, List.mem_cons, List.mem_singleton,
        List.mem_nil_iff, or_false] at *
        rcases hr with (((((h | h) | h) | h) | h) | h) | h <;> simp [h])) ?_
  rw [h₇.v, h₆.get .v2, a₅, a₆]
  exact unzip_wide true _ _ _ _

end
end VG.Proof.MlDsa.AArch64.Arith.Neon
