import VerifiedGarbage.Proof.X448.Arm.Step
import VerifiedGarbage.Proof.Framework.Range

/-!
# X448 on ARMv7: carry propagation
-/

namespace VG.Proof.X448.Arm

open VG VG.Arm VG.Impl.X448.Arm VG.Proof.X448.Radix16
open VG.Proof.X25519.Arm (wp_mov op2_imm wp_ldr wp_dp op2_reg wp_str)

theorem rest_keeps {ws : List Reg} {s t : State} (h : VG.Proof.X25519.Arm.Rest ws s t) : Keeps ws s t :=
  ⟨h.gpr, h.rd, h.wr⟩

theorem zeroCarry_ok (s : State) :
    WP isa (.block [.mov .r5 (.imm 0)]) s fun t =>
      t.gpr .r5 = 0 ∧ t.mem = s.mem ∧ Keeps [.r3, .r5, .r4] s t := by
  refine wp_mov (op2_imm (by decide)) fun t ht => WP.block_nil
    ⟨ht.gpr, ht.mem, rest_keeps (ht.rest (by decide))⟩

/-- An in-place pass only overwrites input limbs it has already consumed. -/
theorem pass_ok {s : State} {base : Addr} (hs : Scr s base) {o a : Nat}
    (ho : o + 112 ≤ 4096) (ha : a + 112 ≤ 4096)
    (hsep : o = a ∨ o + 112 ≤ a ∨ a + 112 ≤ o)
    {f : Nat → Nat} (hf : ∀ i < 28, limbs s.mem base a i = f i)
    (hb : ∀ i < 28, f i ≤ 2 ^ 32 - radix) :
    WP isa (.block (pass o a)) s fun s' =>
      (∀ i < 28, limbs s'.mem base o i = digit f i) ∧
      (s'.gpr .r5).toNat = carry f 28 ∧ Outside base o 112 s.mem s'.mem ∧
      Keeps [.r3, .r5, .r4] s s' := by
  let inv := fun k (t : State) =>
    (∀ i < k, limbs t.mem base o i = digit f i) ∧
    (∀ i, k ≤ i → i < 28 → limbs t.mem base a i = f i) ∧
    (t.gpr .r5).toNat = carry f k ∧ Outside base o 112 s.mem t.mem ∧
    Keeps [.r3, .r5, .r4] s t
  have step : ∀ k t, k < 28 → inv k t → WP isa (.block (carryBlock o a k)) t (inv (k + 1)) := by
    intro k t hk ⟨hlo, hhi, hc, hm, ht⟩
    have hts := hs.of_keeps ht (by decide)
    have he := hhi k (by omega) hk
    have hsum : (word t.mem base (a + 4 * k)).toNat + (t.gpr .r5).toNat < 2 ^ 32 := by
      change limbs t.mem base a k + (t.gpr .r5).toNat < _
      rw [he, hc]
      have hcoeff := hb k hk
      have hcarry := carry_bound (n := k) (fun i hi => hb i (by omega))
      simp only [radix] at hcoeff
      omega
    refine WP.mono (carryStep_ok hts (by omega) (by omega) hsum) fun u ⟨hu, hmem, huKeep⟩ => ?_
    have he' : (word t.mem base (a + 4 * k)).toNat + (t.gpr .r5).toNat = f k + carry f k := by
      change limbs t.mem base a k + (t.gpr .r5).toNat = _
      rw [he, hc]
    rw [he'] at hu hmem
    have out : Outside base (o + 4 * k) 4 t.mem u.mem := by
      rw [hmem]
      exact writeW_outside _ _ _ (by omega)
    refine ⟨?_, ?_, hu, hm.trans (out.mono (by omega) (by omega)), ht.trans huKeep⟩
    · intro i hi
      change (word u.mem base (o + 4 * i)).toNat = _
      rw [hmem, word_write t.mem base (by omega) (by omega)]
      by_cases hik : i = k
      · rw [ite_eq_left hik, hik, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := (f k + carry f k) % radix)
          (Nat.lt_trans (digit_lt f k) (by decide))]
        rfl
      · rw [ite_eq_right hik]
        exact hlo i (by omega)
    · intro i hi hi'
      have sep : a + 4 * i + 4 ≤ o + 4 * k ∨ o + 4 * k + 4 ≤ a + 4 * i := by
        rcases hsep with h | h | h <;> omega
      change (word u.mem base (a + 4 * i)).toNat = _
      rw [out.word sep (by omega)]
      exact hhi i (by omega) hi'
  change WP isa (.block ([.mov .r5 (.imm 0)] ++ (List.range 28).flatMap (carryBlock o a))) s _
  rw [WP.block_append_iff]
  refine WP.mono (zeroCarry_ok s) fun t ⟨hc, hm, ht⟩ => ?_
  refine WP.mono (wp_range_flatMap inv step 28 (by decide) t ?_) fun u ⟨hlo, _, hc, hm, ht⟩ =>
    ⟨hlo, hc, hm, ht⟩
  refine ⟨fun i hi => by omega, (fun i _ hi => ?_), ?_, ?_, ht⟩
  · rw [hm]; exact hf i hi
  · rw [hc]; rfl
  · rw [hm]; exact Outside.refl _ _ _ _

theorem foldStep_ok {s : State} {base : Addr} (hs : Scr s base) {d : Nat}
    (hd : d + 4 ≤ 4096) :
    WP isa (.block [ld .r3 d, .dp .add .r3 .r3 (.reg .r5), st .r3 d]) s
      fun t => t.mem = s.mem.writeW (off base d) (word s.mem base d + s.gpr .r5) ∧
        Keeps [.r3] s t := by
  refine wp_ldr (a := off base d) (by omega) (hs.ea (by omega)) (hs.read (by omega)) fun t ht => ?_
  refine wp_dp (op2_reg _ _) fun u hu => ?_
  refine wp_str (a := off base d) (by omega)
    (by rw [hu.other .r0 (by decide), ht.other .r0 (by decide)]; exact hs.ea (by omega))
    (by rw [hu.wr, ht.wr]; exact hs.write (by omega)) fun v hv => WP.block_nil ⟨?_, ?_⟩
  · rw [hv.mem, hu.mem, ht.mem, hu.gpr]
    change s.mem.writeW _ (t.gpr .r3 + t.gpr .r5) = _
    rw [ht.gpr, ht.other .r5 (by decide)]
  · exact rest_keeps ((ht.rest (by decide)).trans ((hu.rest (by decide)).trans (hv.rest _)))

theorem foldLimb_ok {s : State} {base : Addr} (hs : Scr s base) {k : Nat} (hk : k < 28)
    (hb : limbs s.mem base TMP k + (s.gpr .r5).toNat < 2 ^ 32) :
    WP isa (.block [ld .r3 (TMP + 4 * k), .dp .add .r3 .r3 (.reg .r5),
      st .r3 (TMP + 4 * k)]) s fun t =>
      (∀ i < 28, limbs t.mem base TMP i =
        if i = k then limbs s.mem base TMP i + (s.gpr .r5).toNat else limbs s.mem base TMP i) ∧
      Outside base TMP 112 s.mem t.mem ∧ Keeps [.r3] s t := by
  have hd : TMP + 4 * k + 4 ≤ 4096 := by simp only [TMP]; omega
  refine WP.mono (foldStep_ok hs hd) fun t ⟨hm, ht⟩ => ?_
  refine ⟨?_, ?_, ht⟩
  · intro i hi
    change (word t.mem base (TMP + 4 * i)).toNat = _
    rw [hm, word_write s.mem base (by omega) (by simp only [TMP]; omega)]
    by_cases h : i = k
    · rw [ite_eq_left h, ite_eq_left h, h, BitVec.toNat_add, Nat.mod_eq_of_lt hb]
    · rw [ite_eq_right h, ite_eq_right h]
  · rw [hm]
    exact (writeW_outside _ _ _ (by omega : TMP + 4 * k + 4 ≤ 8192)).mono (by omega) (by omega)

/-- The two stores implement the mathematical carry fold. -/
theorem fold_ok {s : State} {base : Addr} (hs : Scr s base) {f : Nat → Nat}
    (hf : ∀ i < 28, limbs s.mem base TMP i = digit f i)
    (hc : (s.gpr .r5).toNat = carry f 28) (hb : carry f 28 < 2 ^ 16) :
    WP isa (.block fold) s fun s' =>
      (∀ i < 28, limbs s'.mem base TMP i = folded f i) ∧
      Outside base TMP 112 s.mem s'.mem ∧ Keeps [.r3] s s' := by
  have bound : ∀ i < 28, digit f i + carry f 28 < 2 ^ 32 := by
    intro i _
    have h := digit_lt f i
    simp only [radix] at h
    omega
  change WP isa (.block
    (([ld .r3 (TMP + 4 * 0), .dp .add .r3 .r3 (.reg .r5),
       st .r3 (TMP + 4 * 0)] : List Instr) ++
     [ld .r3 (TMP + 4 * 14), .dp .add .r3 .r3 (.reg .r5),
       st .r3 (TMP + 4 * 14)])) s _
  rw [WP.block_append_iff]
  refine WP.mono (foldLimb_ok hs (k := 0) (by decide) (by rw [hf 0 (by decide), hc]; exact bound 0 (by decide)))
    fun t ⟨htf, htm, ht⟩ => ?_
  have htc : (t.gpr .r5).toNat = carry f 28 := by rw [ht.1 _ (by decide), hc]
  refine WP.mono (foldLimb_ok (hs.of_keeps ht (by decide)) (k := 14) (by decide) ?_)
    fun u ⟨huf, hum, hu⟩ => ?_
  · rw [htf 14 (by decide), ite_eq_right (by decide), hf 14 (by decide), htc]
    exact bound 14 (by decide)
  · refine ⟨?_, htm.trans hum, ht.trans hu⟩
    intro i hi
    rw [huf i hi, htf i hi, hf i hi, hc, htc]
    simp only [folded]
    by_cases h0 : i = 0
    · subst i; simp (config := {decide := true}) only [ite_true, ite_false]
    · by_cases h8 : i = 14
      · subst i; simp (config := {decide := true}) only [ite_true, ite_false]
      · simp only [h0, h8, ite_false, false_or, Nat.add_zero]

end VG.Proof.X448.Arm
