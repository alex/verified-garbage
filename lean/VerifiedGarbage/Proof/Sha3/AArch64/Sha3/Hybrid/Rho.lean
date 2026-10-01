import VerifiedGarbage.Proof.Sha3.AArch64.Sha3.Hybrid.Rotate

namespace VG.Proof.Sha3.AArch64.Sha3.Hybrid

open VG VG.AArch64
open VG.Impl.Sha3.AArch64.Sha3.Hybrid
open VG.Impl.Sha3 (rhoOff piSrc)
open VG.Proof.Sha3 (C D B)

def rotWord (A : Spec.Sha3.State) (i : Nat) : BitVec 64 :=
  Proof.Sha3.rotl (A[i]! ^^^ D A (i % 5)) (rhoOff i)

def RotProgress (r : Nat) (A : Spec.Sha3.State) (n : Nat) (s : VG.AArch64.State) : Prop :=
  ∀ i < 25, value s (laneSlot (loc r i)) =
    if 5 * (i % 5) + i / 5 < n then rotWord A i else A[i]!

theorem rotProgress_zero (r : Nat) (A : Spec.Sha3.State) (s : VG.AArch64.State) (ha : Lanes s r A) :
    RotProgress r A 0 s := by
  intro i hi
  rw [ite_eq_right (by omega)]
  exact (ha i hi).trans (getElem!_eq A hi).symm

def RotInv (s₀ : VG.AArch64.State) (r : Nat) (A : Spec.Sha3.State) (n : Nat)
    (s : VG.AArch64.State) : Prop :=
  Keep s₀ s ∧ (∀ j < 5, s.gpr (creg j) = C A j) ∧ RotProgress r A n s

theorem dprep_ok (x : Nat) (s : VG.AArch64.State) (A : Spec.Sha3.State)
    (hc : ∀ j < 5, s.gpr (creg j) = C A j) :
    WP isa (.block [.ror .x .x17 (creg ((x + 1) % 5)) 63,
      .logic .eor .x .x17 .x17 (creg ((x + 4) % 5)), .vop (.dup .d2 .v28 .x17)]) s fun s' =>
      Keep s s' ∧ (∀ j < 5, s'.gpr (creg j) = s.gpr (creg j)) ∧
      vdword (s'.v .v28) 0 = D A x ∧ s'.gpr .x17 = D A x ∧
      ∀ i < 25, value s' (laneSlot i) = value s (laneSlot i) := by
  have hcreg : ∀ j < 5, creg j ≠ .x17 := by decide
  apply WP.of_runBlock
  simp (config := {decide := true}) (disch := omega) only
    [runBlock_cons, runBlock_nil, exec_vop, VOp.eval, exec_ror_x (by decide : 63 < 64),
      exec_logic, State.read, Option.map_some, isa, runStep_some, Option.some.injEq, exists_eq_left',
      RegUpd.gpr_write, RegUpd.gpr_setV, hcreg, Size.bits, BitVec.setWidth_eq, ite_true, ite_false]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · constructor <;> simp (config := {decide := true}) only [RegUpd.gpr_setV, RegUpd.gpr_write,
      ite_false, RegUpd.mem_setV, RegUpd.mem_write, RegUpd.rd_setV, RegUpd.rd_write,
      RegUpd.wr_setV, RegUpd.wr_write, RegUpd.sp_setV, RegUpd.sp_write]
  · intro j hj
    simp only [hcreg j hj, ite_false]
  · simp (disch := omega) only [RegUpd.v_setV_self, vdword_ofVDwords_0, hc, D]
  · simp (disch := omega) only [hc, D]
  · intro i hi
    simp only [value_setV, slot_ne_v i _ vother_temps.1, value_write,
      slot_ne_g i hi _ gother_temps.2.2.2, ite_false]

theorem rotateColumn_ok (r x : Nat) (hx : x < 5) (s₀ : VG.AArch64.State) (A : Spec.Sha3.State)
    (h : RotInv s₀ r A (5 * x) s₀) :
    WP isa (.block (rotateColumn r x)) s₀ (RotInv s₀ r A (5 * (x + 1))) := by
  unfold rotateColumn
  rw [WP.block_append_iff]
  refine (dprep_ok x s₀ A h.2.1).mono fun s₁ ⟨hk, hg, hd, hdg, hv⟩ => ?_
  let inv := fun y s => RotInv s₀ r A (5 * x + y) s ∧ vdword (s.v .v28) 0 = D A x ∧ s.gpr .x17 = D A x
  have hstart : inv 0 s₁ := ⟨⟨hk, fun j hj => (hg j hj).trans (h.2.1 j hj), by
    intro i hi
    rw [hv _ (loc_bound _ _ hi)]
    exact h.2.2 i hi⟩, hd, hdg⟩
  have hloop : WP isa (.block ((List.range 5).flatMap (rotateLane r x))) s₁ (inv 5) := by
    refine wp_range_flatMap (M := isa) inv (fun y s hy ⟨⟨hs, hc, ha⟩, hD, hG⟩ => ?_)
      5 (Nat.le_refl _) s₁ hstart
    refine (rotateLane_ok r x y hx hy s (hG.trans hD.symm)).mono fun s' ⟨hh, hd', hg', hc', hl⟩ => ?_
    refine ⟨⟨hs.trans hh, fun j hj => (hc' j hj).trans (hc j hj), ?_⟩,
      by rw [hd', hD], by rw [hg', hG]⟩
    intro i hi
    rw [hl i hi]
    by_cases he : i = x + 5 * y
    · subst i
      have hm : (x + 5 * y) % 5 = x := by omega
      have hq : (x + 5 * y) / 5 = y := by omega
      simp only [ite_true, ha _ (by omega), hm, hq,
        show ¬5 * x + y < 5 * x + y by omega, ite_false,
        show 5 * x + y < 5 * x + (y + 1) by omega, rotWord, hD]
    · have hn : (5 * (i % 5) + i / 5 < 5 * x + (y + 1)) ↔
          (5 * (i % 5) + i / 5 < 5 * x + y) := by omega
      simp only [he, ite_false, ha i hi, hn]
  exact hloop.mono fun s' hh => by
    have he : 5 * x + 5 = 5 * (x + 1) := by omega
    rw [← he]
    exact hh.1

theorem rotations_ok (r : Nat) (s₀ : VG.AArch64.State) (A : Spec.Sha3.State)
    (ha : Lanes s₀ r A) (hc : ∀ j < 5, s₀.gpr (creg j) = C A j) :
    WP isa (.block ((List.range 5).flatMap (rotateColumn r))) s₀ fun s' =>
      Keep s₀ s' ∧ ∀ x < 5, ∀ y < 5, value s' (rowSlot r x y) = B A x y := by
  have hh : WP isa (.block ((List.range 5).flatMap (rotateColumn r))) s₀
      (fun x => RotInv s₀ r A (5 * 5) x) := by
    refine wp_range_flatMap (M := isa) (fun x => RotInv s₀ r A (5 * x))
      (fun x s hx ⟨hs, hcs, hA⟩ => ?_) 5 (Nat.le_refl _) s₀
      ⟨Keep.refl _, hc, rotProgress_zero r A s₀ ha⟩
    exact (rotateColumn_ok r x hx s A ⟨Keep.refl _, hcs, hA⟩).mono
      fun s' ⟨hk, hc', ha'⟩ => ⟨hs.trans hk, hc', ha'⟩
  refine hh.mono fun s' ⟨hk, _, hp⟩ => ⟨hk, fun x hx y hy => ?_⟩
  have hi : piSrc x y < 25 := by unfold piSrc; omega
  simp only [rowSlot, loc_succ r x y hx, hp _ hi,
    show 5 * (piSrc x y % 5) + piSrc x y / 5 < 5 * 5 by omega, ite_true, rotWord, B]
  have hm : piSrc x y % 5 = (x + 3 * y) % 5 := by unfold piSrc; omega
  rw [hm]

end VG.Proof.Sha3.AArch64.Sha3.Hybrid
