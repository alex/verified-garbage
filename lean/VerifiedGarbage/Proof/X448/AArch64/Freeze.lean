import VerifiedGarbage.Proof.X448.AArch64.FreezePrep
import VerifiedGarbage.Proof.X448.AArch64.Select
import VerifiedGarbage.Proof.X448.AArch64.Env

/-!
# X448 on AArch64: canonical reduction

Untrusted: everything here is checked by Lean. The final carry selects the
unique representative below the prime, using only a mask on secret data.
-/

namespace VG.Proof.X448.AArch64

open VG VG.AArch64 VG.Impl.X448.AArch64

theorem freezeMask_ok {s : State} {c : Nat} (hc : (s.gpr .x6).toNat = c) (hb : c < 2) :
    WP isa (.block [.movz .x .x7 0 0, .sub .x .x7 .x7 .x6]) s fun t =>
      t.gpr .x7 = mask (decide (c = 1)) ∧ t.mem = s.mem ∧ Keeps [.x7] s t := by
  have he : s.gpr .x6 = BitVec.ofNat 64 c := by rw [← hc, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have hm : ∀ a < 2, BitVec.setWidth 64 (0 : BitVec 16) - BitVec.ofNat 64 a =
      mask (decide (a = 1)) := by decide
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, State.read, Size.bits,
    Nat.reduceLT, Nat.reduceMul, BitVec.shiftLeft_zero, BitVec.setWidth_eq,
    RegUpd.gpr_write, he, ite_true, ite_false, reduceCtorEq, Option.some.injEq, exists_eq_left']
  refine ⟨hm c hb, rfl, (fun r hr => ?_), rfl, rfl⟩
  simp only [List.mem_singleton] at hr
  simp only [RegUpd.gpr_write, hr, ite_false]

theorem freeze_ok {s : State} {base : Addr} (hs : Scr s base) (hb : Bounded s.mem base X2) :
    WP isa (.block freeze) s fun t =>
      Bounded t.mem base X2 ∧ fe t.mem base X2 = fe s.mem base X2 % Spec.X448.P ∧
      FieldMem base X2 s.mem t.mem ∧ Keeps workRegs s t := by
  change WP isa (.block ((copy TMP X2 ++ [0, 8].flatMap (fun i =>
    [ld .x4 (TMP + 8 * i), .addImm .x .x4 .x4 1,
      st .x4 (TMP + 8 * i)])) ++ (pass TMP TMP ++
    (([.movz .x .x7 0 0, .sub .x .x7 .x7 .x6] : List Instr) ++
      (List.range 16).flatMap selectStep)))) s _
  rw [WP.block_append_iff]
  refine WP.mono (freezePrep_ok hs hb) fun t ⟨tf, tm, tk⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (pass_ok (hs.of_keeps tk (by decide)) (by decide) (by decide) (by decide) (by decide) (Or.inl rfl)
    tf (freezeCoeff_bound hb)) fun u ⟨uf, uc, um, uk⟩ => ?_
  have cb : carry (freezeCoeff (limbs s.mem base X2)) 16 < 2 := by
    rw [freeze_carry hb]; split <;> decide
  rw [WP.block_append_iff]
  refine WP.mono (freezeMask_ok uc cb) fun v ⟨vc, vm, vk⟩ => ?_
  have vs := ((hs.of_keeps tk (by decide)).of_keeps uk (by decide)).of_keeps vk (by decide)
  refine WP.mono (select_ok vs vc) fun w ⟨wf, wm, wk⟩ => ?_
  have outside : Outside base TMP 128 s.mem v.mem := by rw [vm]; exact tm.trans um
  have lf : ∀ i < 16, limbs w.mem base X2 i =
      if carry (freezeCoeff (limbs s.mem base X2)) 16 = 1 then
        digit (freezeCoeff (limbs s.mem base X2)) i else limbs s.mem base X2 i := by
    intro i hi
    rw [wf i hi, outside.limbs (d := X2) (by decide) (by decide) hi, vm, uf i hi]
    simp only [decide_eq_true_eq]
  refine ⟨?_, ?_, (FieldMem.work outside (by decide) (by decide)).trans (FieldMem.output wm),
    (tk.mono ?_).trans ((uk.mono ?_).trans ((vk.mono ?_).trans (wk.mono ?_)))⟩
  · intro i hi; rw [lf i hi]; split
    · exact digit_lt _ _
    · exact hb i hi
  · change valN (limbs w.mem base X2) 16 = _
    rw [valN_congr lf]
    by_cases h : carry (freezeCoeff (limbs s.mem base X2)) 16 = 1
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

end VG.Proof.X448.AArch64
