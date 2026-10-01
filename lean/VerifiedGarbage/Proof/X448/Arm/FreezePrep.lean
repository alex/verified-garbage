import VerifiedGarbage.Proof.X448.Arm.Copy

/-!
# X448 on ARMv7: preparing canonical reduction

Untrusted: everything here is checked by Lean. Adding one in limbs zero
and fourteen implements the addition of 1 + 2²²⁴ before carry propagation.
-/

namespace VG.Proof.X448.Arm

open VG VG.Arm VG.Impl.X448.Arm VG.Proof.X448.Radix16

theorem incrementStep_ok {s : State} {base : Addr} (hs : Scr s base) {d : Nat}
    (hd : d + 4 ≤ 4096) :
    WP isa (.block [ld .r3 d, .dp .add .r3 .r3 (.imm 1), st .r3 d]) s
      fun s' => s'.mem = s.mem.writeW (off base d) (word s.mem base d + (1 : BitVec 32)) ∧
        Keeps [.r3] s s' := by
  refine load_ok hs hd fun t ht => ?_
  refine VG.Proof.X25519.Arm.wp_dp (VG.Proof.X25519.Arm.op2_imm (by decide)) fun u hu => ?_
  refine store_ok ((hs.of_upd ht (by decide) (by decide)).of_upd hu (by decide) (by decide)) hd
    fun v hv => WP.block_nil ⟨?_, ?_⟩
  · rw [hv.mem, hu.mem, ht.mem, hu.gpr, ht.gpr]; rfl
  · exact rest_keeps ((ht.rest (by decide)).trans ((hu.rest (by decide)).trans (hv.rest _)))

theorem incrementLimb_ok {s : State} {base : Addr} (hs : Scr s base) {k : Nat} (hk : k < 28)
    (hb : limbs s.mem base TMP k + 1 < 2 ^ 32) :
    WP isa (.block [ld .r3 (TMP + 4 * k), .dp .add .r3 .r3 (.imm 1),
      st .r3 (TMP + 4 * k)]) s fun t =>
      (∀ i < 28, limbs t.mem base TMP i =
        if i = k then limbs s.mem base TMP i + 1 else limbs s.mem base TMP i) ∧
      Outside base TMP 112 s.mem t.mem ∧ Keeps [.r3] s t := by
  have hd : TMP + 4 * k + 4 ≤ 4096 := by simp only [TMP]; omega
  refine WP.mono (incrementStep_ok hs hd) fun t ⟨hm, ht⟩ => ?_
  refine ⟨?_, ?_, ht⟩
  · intro i hi
    change (word t.mem base (TMP + 4 * i)).toNat = _
    rw [hm, word_write s.mem base (by omega) (by simp only [TMP]; omega)]
    by_cases h : i = k
    · rw [ite_eq_left h, ite_eq_left h, h, BitVec.toNat_add]
      change (limbs s.mem base TMP k + 1) % 2 ^ 32 = _
      exact Nat.mod_eq_of_lt hb
    · rw [ite_eq_right h, ite_eq_right h]
  · rw [hm]
    exact (writeW_outside _ _ _ (by omega)).mono (by omega) (by omega)

theorem freezePrep_ok {s : State} {base : Addr} (hs : Scr s base) (hb : Bounded s.mem base X2) :
    WP isa (.block (copy TMP X2 ++ [0, 14].flatMap (fun i =>
      [ld .r3 (TMP + 4 * i), .dp .add .r3 .r3 (.imm 1),
        st .r3 (TMP + 4 * i)]))) s fun t =>
      (∀ i < 28, limbs t.mem base TMP i = freezeCoeff (limbs s.mem base X2) i) ∧
      Outside base TMP 112 s.mem t.mem ∧ Keeps clob s t := by
  rw [WP.block_append_iff]
  refine WP.mono (copy_ok hs (by decide) (by decide) (by decide)) fun t ⟨tf, tm, tk⟩ => ?_
  have bound : ∀ i < 28, limbs s.mem base X2 i + 1 < 2 ^ 32 := by
    intro i hi; have h := hb i hi; simp only [radix] at h; omega
  change WP isa (.block
    (([ld .r3 (TMP + 4 * 0), .dp .add .r3 .r3 (.imm 1),
       st .r3 (TMP + 4 * 0)] : List Instr) ++
     [ld .r3 (TMP + 4 * 14), .dp .add .r3 .r3 (.imm 1),
       st .r3 (TMP + 4 * 14)])) t _
  rw [WP.block_append_iff]
  refine WP.mono (incrementLimb_ok (hs.of_keeps tk (by decide)) (k := 0) (by decide)
    (by rw [tf 0 (by decide)]; exact bound 0 (by decide))) fun u ⟨uf, um, uk⟩ => ?_
  refine WP.mono (incrementLimb_ok ((hs.of_keeps tk (by decide)).of_keeps uk (by decide))
    (k := 14) (by decide) (by
      rw [uf 14 (by decide), ite_eq_right (by decide), tf 14 (by decide)]
      exact bound 14 (by decide))) fun v ⟨vf, vm, vk⟩ => ?_
  refine ⟨?_, tm.trans (um.trans vm), tk.trans ((uk.trans vk).mono ?_)⟩
  · intro i hi
    rw [vf i hi, uf i hi, tf i hi]
    simp only [freezeCoeff]
    by_cases h0 : i = 0
    · subst i; simp (config := {decide := true}) only [ite_true, ite_false]
    · by_cases h8 : i = 14
      · subst i; simp (config := {decide := true}) only [ite_true, ite_false]
      · simp only [h0, h8, ite_false, false_or, Nat.add_zero]
  · intro r hr; simp only [List.mem_singleton] at hr; subst r; decide

end VG.Proof.X448.Arm
