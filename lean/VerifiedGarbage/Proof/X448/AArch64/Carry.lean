import VerifiedGarbage.Proof.X448.AArch64.Step
import VerifiedGarbage.Proof.Framework.Range

/-!
# X448 on AArch64: carry propagation

The sixteen machine steps implement `digit` and `carry`; the inputs may be
normalized in place.
-/

namespace VG.Proof.X448.AArch64

open VG VG.AArch64 VG.Impl.X448.AArch64

theorem zeroCarry_ok (s : State) :
    WP isa (.block [.movz .x .x6 0 0]) s fun s' =>
      s'.gpr .x6 = 0 ∧ s'.mem = s.mem ∧ Keeps [.x4, .x6, .x5] s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, Size.bits,
    Nat.reduceMul, Nat.reduceLT, ite_true, BitVec.shiftLeft_zero, BitVec.setWidth_eq,
    RegUpd.gpr_write, Option.some.injEq, exists_eq_left']
  refine ⟨rfl, rfl, (fun r hr => ?_), rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [RegUpd.gpr_write, hr.2.1, ite_false]

/-- An in-place pass only overwrites input limbs it has already consumed. -/
theorem pass_ok {s : State} {base : Addr} (hs : Scr s base) {o a : Nat}
    (ho : o + 128 ≤ 8192) (ha : a + 128 ≤ 8192) (ho8 : o % 8 = 0) (ha8 : a % 8 = 0)
    (hsep : o = a ∨ o + 128 ≤ a ∨ a + 128 ≤ o)
    {f : Nat → Nat} (hf : ∀ i < 16, limbs s.mem base a i = f i)
    (hb : ∀ i < 16, f i < 2 ^ 62) :
    WP isa (.block (pass o a)) s fun s' =>
      (∀ i < 16, limbs s'.mem base o i = digit f i) ∧
      (s'.gpr .x6).toNat = carry f 16 ∧ Outside base o 128 s.mem s'.mem ∧
      Keeps [.x4, .x6, .x5] s s' := by
  let inv := fun k (t : State) =>
    (∀ i < k, limbs t.mem base o i = digit f i) ∧
    (∀ i, k ≤ i → i < 16 → limbs t.mem base a i = f i) ∧
    (t.gpr .x6).toNat = carry f k ∧ Outside base o 128 s.mem t.mem ∧
    Keeps [.x4, .x6, .x5] s t
  have step : ∀ k t, k < 16 → inv k t → WP isa (.block (carryStep o a k)) t (inv (k + 1)) := by
    intro k t hk ⟨hlo, hhi, hc, hm, ht⟩
    have hts := hs.of_keeps ht (by decide)
    have he := hhi k (by omega) hk
    have hsum : (word t.mem base (a + 8 * k)).toNat + (t.gpr .x6).toNat < 2 ^ 64 := by
      change limbs t.mem base a k + (t.gpr .x6).toNat < _
      rw [he, hc]
      have := hb k hk
      have := carry_bound (n := k) (fun i hi => hb i (by omega))
      omega
    refine WP.mono (carryStep_ok hts (by omega) (by omega) ho8 ha8 hsum) fun u ⟨hu, hmem, huKeep⟩ => ?_
    have he' : (word t.mem base (a + 8 * k)).toNat + (t.gpr .x6).toNat = f k + carry f k := by
      change limbs t.mem base a k + (t.gpr .x6).toNat = _
      rw [he, hc]
    rw [he'] at hu hmem
    have out : Outside base (o + 8 * k) 8 t.mem u.mem := by
      rw [hmem]
      exact writeW_outside _ _ _ (by omega)
    refine ⟨?_, ?_, hu, hm.trans (out.mono (by omega) (by omega)), ht.trans huKeep⟩
    · intro i hi
      change (word u.mem base (o + 8 * i)).toNat = _
      rw [hmem, word_write t.mem base (by omega) (by omega)]
      by_cases hik : i = k
      · rw [ite_eq_left hik, hik, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := (f k + carry f k) % radix)
          (Nat.lt_trans (digit_lt f k) (by decide))]
        rfl
      · rw [ite_eq_right hik]
        exact hlo i (by omega)
    · intro i hi hi'
      have sep : a + 8 * i + 8 ≤ o + 8 * k ∨ o + 8 * k + 8 ≤ a + 8 * i := by
        rcases hsep with h | h | h <;> omega
      change (word u.mem base (a + 8 * i)).toNat = _
      rw [out.word sep (by omega)]
      exact hhi i (by omega) hi'
  change WP isa (.block ([.movz .x .x6 0 0] ++ (List.range 16).flatMap (carryStep o a))) s _
  rw [WP.block_append_iff]
  refine WP.mono (zeroCarry_ok s) fun t ⟨hc, hm, ht⟩ => ?_
  refine WP.mono (wp_range_flatMap inv step 16 (by decide) t ?_) fun u ⟨hlo, _, hc, hm, ht⟩ =>
    ⟨hlo, hc, hm, ht⟩
  refine ⟨fun i hi => by omega, (fun i _ hi => ?_), ?_, ?_, ht⟩
  · rw [hm]; exact hf i hi
  · rw [hc]; rfl
  · rw [hm]; exact Outside.refl _ _ _ _

/-- Fold the carry into one word, preserving `x6` for the other fold. -/
theorem foldStep_ok {s : State} {base : Addr} (hs : Scr s base) {d : Nat}
    (hd : d + 8 ≤ 8192) (hd8 : d % 8 = 0) :
    WP isa (.block [ld .x4 d, .add .x .x4 .x4 .x6, st .x4 d]) s
      fun s' => s'.mem = s.mem.writeW (off base d) (word s.mem base d + s.gpr .x6) ∧
        Keeps [.x4] s s' := by
  have l := hs.read hd
  have w := hs.write hd
  have enc : d % 8 = 0 ∧ d < 32768 := ⟨hd8, by omega⟩
  apply WP.of_runBlock
  simp only [ld, st, runBlock_cons, runStep_some, runBlock_nil, exec, Size.bytes,
    Size.bits, addr, enc, State.read, State.load, State.store, hs.x3, l, w,
    RegUpd.gpr_write, RegUpd.mem_write, RegUpd.wr_write, BitVec.setWidth_eq,
    read8_eq, write8_eq, Option.bind_some, Option.map_some, and_self, ite_true, ite_false, reduceCtorEq,
    Option.some.injEq, exists_eq_left']
  refine ⟨trivial, (fun r hr => ?_), rfl, rfl⟩
  simp only [List.mem_singleton] at hr
  simp only [RegUpd.gpr_write, hr, ite_false]

theorem foldLimb_ok {s : State} {base : Addr} (hs : Scr s base) {k : Nat} (hk : k < 16)
    (hb : limbs s.mem base TMP k + (s.gpr .x6).toNat < 2 ^ 64) :
    WP isa (.block [ld .x4 (TMP + 8 * k), .add .x .x4 .x4 .x6,
      st .x4 (TMP + 8 * k)]) s fun t =>
      (∀ i < 16, limbs t.mem base TMP i =
        if i = k then limbs s.mem base TMP i + (s.gpr .x6).toNat else limbs s.mem base TMP i) ∧
      Outside base TMP 128 s.mem t.mem ∧ Keeps [.x4] s t := by
  have hd : TMP + 8 * k + 8 ≤ 8192 := by simp only [TMP]; omega
  refine WP.mono (foldStep_ok hs hd (by simp only [TMP]; omega)) fun t ⟨hm, ht⟩ => ?_
  refine ⟨?_, ?_, ht⟩
  · intro i hi
    change (word t.mem base (TMP + 8 * i)).toNat = _
    rw [hm, word_write s.mem base (by omega) (by simp only [TMP]; omega)]
    by_cases h : i = k
    · rw [ite_eq_left h, ite_eq_left h, h, BitVec.toNat_add, Nat.mod_eq_of_lt hb]
    · rw [ite_eq_right h, ite_eq_right h]
  · rw [hm]
    exact (writeW_outside _ _ _ hd).mono (by omega) (by omega)

/-- The two stores implement the mathematical carry fold. -/
theorem fold_ok {s : State} {base : Addr} (hs : Scr s base) {f : Nat → Nat}
    (hf : ∀ i < 16, limbs s.mem base TMP i = digit f i)
    (hc : (s.gpr .x6).toNat = carry f 16) (hb : carry f 16 < 2 ^ 35) :
    WP isa (.block fold) s fun s' =>
      (∀ i < 16, limbs s'.mem base TMP i = folded f i) ∧
      Outside base TMP 128 s.mem s'.mem ∧ Keeps [.x4] s s' := by
  have bound : ∀ i < 16, digit f i + carry f 16 < 2 ^ 64 := by
    intro i _
    have h := digit_lt f i
    simp only [radix] at h
    omega
  change WP isa (.block
    (([ld .x4 (TMP + 8 * 0), .add .x .x4 .x4 .x6,
       st .x4 (TMP + 8 * 0)] : List Instr) ++
     [ld .x4 (TMP + 8 * 8), .add .x .x4 .x4 .x6,
       st .x4 (TMP + 8 * 8)])) s _
  rw [WP.block_append_iff]
  refine WP.mono (foldLimb_ok hs (k := 0) (by decide) (by rw [hf 0 (by decide), hc]; exact bound 0 (by decide)))
    fun t ⟨htf, htm, ht⟩ => ?_
  have htc : (t.gpr .x6).toNat = carry f 16 := by rw [ht.1 _ (by decide), hc]
  refine WP.mono (foldLimb_ok (hs.of_keeps ht (by decide)) (k := 8) (by decide) ?_)
    fun u ⟨huf, hum, hu⟩ => ?_
  · rw [htf 8 (by decide), ite_eq_right (by decide), hf 8 (by decide), htc]
    exact bound 8 (by decide)
  · refine ⟨?_, htm.trans hum, ht.trans hu⟩
    intro i hi
    rw [huf i hi, htf i hi, hf i hi, hc, htc]
    simp only [folded]
    by_cases h0 : i = 0
    · subst i; simp (config := {decide := true}) only [ite_true, ite_false]
    · by_cases h8 : i = 8
      · subst i; simp (config := {decide := true}) only [ite_true, ite_false]
      · simp only [h0, h8, ite_false, false_or, Nat.add_zero]

end VG.Proof.X448.AArch64
