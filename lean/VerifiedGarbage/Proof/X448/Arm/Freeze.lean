import VerifiedGarbage.Proof.X448.Arm.FreezePrep
import VerifiedGarbage.Proof.X448.Arm.Select
import VerifiedGarbage.Proof.X448.Arm.Env

/-!
# X448 on ARMv7: canonical reduction

Untrusted: everything here is checked by Lean. The final carry selects the
unique representative below the prime, using only a mask on secret data.
-/

namespace VG.Proof.X448.Arm

open VG VG.Arm VG.Impl.X448.Arm VG.Proof.X448.Radix16

theorem freezeMask_ok {s : State} {c : Nat} (hc : (s.gpr .r5).toNat = c) (hb : c < 2) :
    WP isa (.block [.mov .r4 (.imm 0), .dp .sub .r4 .r4 (.reg .r5)]) s fun t =>
      t.gpr .r4 = mask (decide (c = 1)) ∧ t.mem = s.mem ∧ Keeps [.r4] s t := by
  have he : s.gpr .r5 = BitVec.ofNat 32 c := by rw [← hc, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have hm : ∀ a < 2, (0 : BitVec 32) - BitVec.ofNat 32 a = mask (decide (a = 1)) := by decide
  refine VG.Proof.X25519.Arm.wp_mov (VG.Proof.X25519.Arm.op2_imm (by decide)) fun t ht => ?_
  refine VG.Proof.X25519.Arm.wp_dp (VG.Proof.X25519.Arm.op2_reg _ _) fun u hu => WP.block_nil ⟨?_, ?_, ?_⟩
  · rw [hu.gpr]; change t.gpr .r4 - t.gpr .r5 = _
    rw [ht.gpr, ht.other .r5 (by decide), he]; exact hm c hb
  · exact hu.mem.trans ht.mem
  · exact rest_keeps ((ht.rest (by decide)).trans (hu.rest (by decide)))

theorem freeze_ok {s : State} {base : Addr} (hs : Scr s base) (hb : Bounded s.mem base X2) :
    WP isa (.block freeze) s fun t =>
      Bounded t.mem base X2 ∧ fe t.mem base X2 = fe s.mem base X2 % Spec.X448.P ∧
      FieldMem base X2 s.mem t.mem ∧ Keeps workRegs s t := by
  change WP isa (.block ((copy TMP X2 ++ [0, 14].flatMap (fun i =>
    [ld .r3 (TMP + 4 * i), .dp .add .r3 .r3 (.imm 1),
      st .r3 (TMP + 4 * i)])) ++ (pass TMP TMP ++
    (([.mov .r4 (.imm 0), .dp .sub .r4 .r4 (.reg .r5)] : List Instr) ++
      (List.range 28).flatMap selectStep)))) s _
  rw [WP.block_append_iff]
  refine WP.mono (freezePrep_ok hs hb) fun t ⟨tf, tm, tk⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (pass_ok (hs.of_keeps tk (by decide)) (by decide) (by decide) (Or.inl rfl)
    tf (fun i hi => Nat.le_of_lt (freezeCoeff_bound hb i hi))) fun u ⟨uf, uc, um, uk⟩ => ?_
  have cb : carry (freezeCoeff (limbs s.mem base X2)) 28 < 2 := by
    rw [freeze_carry hb]; split <;> decide
  rw [WP.block_append_iff]
  refine WP.mono (freezeMask_ok uc cb) fun v ⟨vc, vm, vk⟩ => ?_
  have vs := ((hs.of_keeps tk (by decide)).of_keeps uk (by decide)).of_keeps vk (by decide)
  refine WP.mono (select_ok vs vc) fun w ⟨wf, wm, wk⟩ => ?_
  have outside : Outside base TMP 112 s.mem v.mem := by rw [vm]; exact tm.trans um
  have lf : ∀ i < 28, limbs w.mem base X2 i =
      if carry (freezeCoeff (limbs s.mem base X2)) 28 = 1 then
        digit (freezeCoeff (limbs s.mem base X2)) i else limbs s.mem base X2 i := by
    intro i hi
    rw [wf i hi, outside.limbs (d := X2) (by decide) (by decide) hi, vm, uf i hi]
    simp only [decide_eq_true_eq]
  refine ⟨?_, ?_, (FieldMem.work outside (by decide) (by decide)).trans (FieldMem.output wm),
    (tk.mono ?_).trans ((uk.mono ?_).trans ((vk.mono ?_).trans (wk.mono ?_)))⟩
  · intro i hi; rw [lf i hi]; split
    · exact digit_lt _ _
    · exact hb i hi
  · change valN (limbs w.mem base X2) 28 = _
    rw [valN_congr lf]
    by_cases h : carry (freezeCoeff (limbs s.mem base X2)) 28 = 1
    · simp only [h, ite_true]
      exact (ite_eq_left h).symm.trans (freeze_value hb)
    · simp only [h, ite_false]
      exact (ite_eq_right h).symm.trans (freeze_value hb)
  · intro r hr; exact List.mem_cons_of_mem _ hr
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> decide
  · intro r hr; simp only [List.mem_singleton] at hr; subst r; decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> decide

end VG.Proof.X448.Arm
