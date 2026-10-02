import VerifiedGarbage.Proof.X448.AArch64.Copy
import VerifiedGarbage.Proof.X448.Freeze

/-!
# X448 on AArch64: preparing canonical reduction

Adding one in limbs zero and eight implements the addition of 1 + 2²²⁴ before
carry propagation.
-/

namespace VG.Proof.X448.AArch64

open VG VG.AArch64 VG.Impl.X448.AArch64

theorem incrementStep_ok {s : State} {base : Addr} (hs : Scr s base) {d : Nat}
    (hd : d + 8 ≤ 8192) (hd8 : d % 8 = 0) :
    WP isa (.block [ld .x4 d, .addImm .x .x4 .x4 1, st .x4 d]) s
      fun s' => s'.mem = s.mem.writeW (off base d) (word s.mem base d + (1 : BitVec 64)) ∧
        Keeps [.x4] s s' := by
  have l := hs.read hd
  have w := hs.write hd
  have enc : d % 8 = 0 ∧ d < 32768 := ⟨hd8, by omega⟩
  apply WP.of_runBlock
  simp only [ld, st, runBlock_cons, runStep_some, runBlock_nil, exec, addr, Size.bytes,
    State.read, State.load, State.store, RegUpd.gpr_write, RegUpd.mem_write,
    RegUpd.wr_write, BitVec.setWidth_eq, enc, and_self, hs.x3, l, w,
    Nat.reduceLT, ite_true, ite_false, reduceCtorEq, Option.map_some, Option.bind_some,
    read8_eq, write8_eq, Option.some.injEq, exists_eq_left']
  refine ⟨rfl, (fun r hr => ?_), rfl, rfl⟩
  simp only [List.mem_singleton] at hr
  simp only [RegUpd.gpr_write, hr, ite_false]

theorem incrementLimb_ok {s : State} {base : Addr} (hs : Scr s base) {k : Nat} (hk : k < 16)
    (hb : limbs s.mem base TMP k + 1 < 2 ^ 64) :
    WP isa (.block [ld .x4 (TMP + 8 * k), .addImm .x .x4 .x4 1,
      st .x4 (TMP + 8 * k)]) s fun t =>
      (∀ i < 16, limbs t.mem base TMP i =
        if i = k then limbs s.mem base TMP i + 1 else limbs s.mem base TMP i) ∧
      Outside base TMP 128 s.mem t.mem ∧ Keeps [.x4] s t := by
  have hd : TMP + 8 * k + 8 ≤ 8192 := by simp only [TMP]; omega
  refine WP.mono (incrementStep_ok hs hd (by simp only [TMP]; omega)) fun t ⟨hm, ht⟩ => ?_
  refine ⟨?_, ?_, ht⟩
  · intro i hi
    change (word t.mem base (TMP + 8 * i)).toNat = _
    rw [hm, word_write s.mem base (by omega) (by simp only [TMP]; omega)]
    by_cases h : i = k
    · rw [ite_eq_left h, ite_eq_left h, h, BitVec.toNat_add]
      change (limbs s.mem base TMP k + 1) % 2 ^ 64 = _
      exact Nat.mod_eq_of_lt hb
    · rw [ite_eq_right h, ite_eq_right h]
  · rw [hm]
    exact (writeW_outside _ _ _ hd).mono (by omega) (by omega)


theorem freezePrep_ok {s : State} {base : Addr} (hs : Scr s base) (hb : Bounded s.mem base X2) :
    WP isa (.block (copy TMP X2 ++ [0, 8].flatMap (fun i =>
      [ld .x4 (TMP + 8 * i), .addImm .x .x4 .x4 1,
        st .x4 (TMP + 8 * i)]))) s fun t =>
      (∀ i < 16, limbs t.mem base TMP i = freezeCoeff (limbs s.mem base X2) i) ∧
      Outside base TMP 128 s.mem t.mem ∧ Keeps clob s t := by
  rw [WP.block_append_iff]
  refine WP.mono (copy_ok hs (by decide) (by decide) (by decide) (by decide) (by decide)) fun t ⟨tf, tm, tk⟩ => ?_
  have bound : ∀ i < 16, limbs s.mem base X2 i + 1 < 2 ^ 64 := by
    intro i hi; have h := hb i hi; simp only [radix] at h; omega
  change WP isa (.block
    (([ld .x4 (TMP + 8 * 0), .addImm .x .x4 .x4 1,
       st .x4 (TMP + 8 * 0)] : List Instr) ++
     [ld .x4 (TMP + 8 * 8), .addImm .x .x4 .x4 1,
       st .x4 (TMP + 8 * 8)])) t _
  rw [WP.block_append_iff]
  refine WP.mono (incrementLimb_ok (hs.of_keeps tk (by decide)) (k := 0) (by decide)
    (by rw [tf 0 (by decide)]; exact bound 0 (by decide))) fun u ⟨uf, um, uk⟩ => ?_
  refine WP.mono (incrementLimb_ok ((hs.of_keeps tk (by decide)).of_keeps uk (by decide))
    (k := 8) (by decide) (by
      rw [uf 8 (by decide), ite_eq_right (by decide), tf 8 (by decide)]
      exact bound 8 (by decide))) fun v ⟨vf, vm, vk⟩ => ?_
  refine ⟨?_, tm.trans (um.trans vm), tk.trans ((uk.trans vk).mono ?_)⟩
  · intro i hi
    rw [vf i hi, uf i hi, tf i hi]
    simp only [freezeCoeff]
    by_cases h0 : i = 0
    · subst i; simp (config := {decide := true}) only [ite_true, ite_false]
    · by_cases h8 : i = 8
      · subst i; simp (config := {decide := true}) only [ite_true, ite_false]
      · simp only [h0, h8, ite_false, false_or, Nat.add_zero]
  · intro r hr; simp only [List.mem_singleton] at hr; subst r; decide

end VG.Proof.X448.AArch64
