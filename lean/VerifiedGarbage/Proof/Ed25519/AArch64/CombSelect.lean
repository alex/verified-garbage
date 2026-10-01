import VerifiedGarbage.Proof.Ed25519.AArch64.CombDigit
import VerifiedGarbage.Proof.Ed25519.AArch64.Field
import VerifiedGarbage.Proof.Ed25519.AArch64.CounterKeep

/-!
# The comb's constant-time selection

Untrusted. With `maskReg k` all ones exactly for `k = |d|` and `x22` the bit
of `|d| = 0`, `selectField` ORs every candidate's words, each ANDed with its
mask, into `x4`–`x7`, so only the candidate `|d|` survives, and stores them.
-/

namespace VG.Proof.Ed25519.AArch64

open VG VG.AArch64 VG.Impl.Ed25519 VG.Impl.Ed25519.AArch64 VG.Proof.Ed25519 VG.Proof.X25519
open Word64

private theorem mask9 : ∀ k < 9, maskReg k ≠ .x9 := by decide
private theorem maskW : ∀ k < 9, ∀ w < 4, maskReg k ≠ wordReg w := by decide
private theorem word9 : ∀ w < 4, wordReg w ≠ .x9 := by decide
private theorem word0 : ∀ w < 4, wordReg w ≠ .x0 := by decide
private theorem wordMem : ∀ w < 4, wordReg w ∈ [Reg.x4, .x5, .x6, .x7] := by decide

private theorem regs_fact (k : Nat) (hk : k < 9) (w : Nat) (hw : w < 4) :
    maskReg k ≠ .x9 ∧ maskReg k ≠ wordReg w ∧ wordReg w ≠ .x9 ∧ wordReg w ≠ .x0 ∧
      wordReg w ∈ [Reg.x4, .x5, .x6, .x7] :=
  ⟨mask9 k hk, maskW k hk w hw, word9 w hw, word0 w hw, wordMem w hw⟩

private theorem or_zero' (x : BitVec 64) : x ||| 0 = x := by ext i; simp

theorem selectWord_ok (s : State) (v : Spec.X25519.Fe) {k w : Nat} (hk : k < 9) (hw : w < 4) :
    WP isa (.block (selectWord v k w)) s fun t =>
      t.gpr (wordReg w) = s.gpr (wordReg w) ||| (feWord v w &&& s.gpr (maskReg k)) ∧
      Keeps [.x9, wordReg w] s t := by
  obtain ⟨hk9, hkw, hw9, _, _⟩ := regs_fact k hk w hw
  rw [selectWord, WP.block_append_iff]
  refine WP.mono (const64_ok s .x9 (feWord v w)) fun a ⟨a9, ka⟩ => ?_
  have am : a.gpr (maskReg k) = s.gpr (maskReg k) := ka.gpr _ (by simpa using hk9)
  have aw : a.gpr (wordReg w) = s.gpr (wordReg w) := ka.gpr _ (by simpa using hw9)
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, read_x,
    Option.some.injEq, exists_eq_left']
  refine ⟨?_, ⟨fun r hr => ?_, ka.mem, ka.rd, ka.wr, ka.sp⟩⟩
  · rw [RegUpd.gpr_write_self, BitVec.setWidth_eq, RegUpd.gpr_write_of_ne _ _ _ hw9,
      RegUpd.gpr_write_self, BitVec.setWidth_eq, a9, am, aw]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [RegUpd.gpr_write_of_ne _ _ _ hr.2, RegUpd.gpr_write_of_ne _ _ _ hr.1,
      ka.gpr _ (by simpa using hr.1)]

theorem selectCandPrefix_ok (s : State) (v : Spec.X25519.Fe) {k : Nat} (hk : k < 9) (n : Nat)
    (hn : n ≤ 4) :
    WP isa (.block ((List.range n).flatMap fun w => selectWord v k w)) s fun t =>
      (∀ w < 4, t.gpr (wordReg w) =
        s.gpr (wordReg w) ||| (if w < n then feWord v w &&& s.gpr (maskReg k) else 0)) ∧
      Keeps [.x9, .x4, .x5, .x6, .x7] s t := by
  induction n with
  | zero =>
    exact WP.block_nil ⟨fun w _ => by simp, ⟨fun _ _ => rfl, rfl, rfl, rfl, rfl⟩⟩
  | succ n ih =>
    rw [List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil,
      WP.block_append_iff]
    refine WP.mono (ih (by omega)) fun t ⟨tv, kt⟩ => ?_
    obtain ⟨hk9, _, _, _, hwm⟩ := regs_fact k hk n (by omega)
    have tm : t.gpr (maskReg k) = s.gpr (maskReg k) := kt.gpr _ (by
      have : ∀ k < 9, maskReg k ∉ [Reg.x9, .x4, .x5, .x6, .x7] := by decide
      exact this k hk)
    refine WP.mono (selectWord_ok t v hk (by omega : n < 4)) fun u ⟨uv, ku⟩ => ?_
    refine ⟨fun w hw => ?_, kt.trans (ku.mono (by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr hwm ⊢
      rcases hr with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr hwm))⟩
    by_cases hwn : w = n
    · subst hwn
      rw [uv, tv w hw, tm]
      simp only [Nat.lt_irrefl, ↓reduceIte, Nat.lt_add_one, or_zero']
    · have hne : wordReg w ≠ wordReg n := by
        have : ∀ a < 4, ∀ b < 4, a ≠ b → wordReg a ≠ wordReg b := by decide
        exact this w hw n (by omega) hwn
      rw [ku.gpr _ (by
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
        exact ⟨(regs_fact k hk w hw).2.2.1, hne⟩), tv w hw]
      by_cases hwl : w < n
      · simp only [hwl, ↓reduceIte, show w < n + 1 by omega]
      · simp only [hwl, ↓reduceIte, show ¬ w < n + 1 by omega]

theorem selectCand_ok (s : State) (v : Spec.X25519.Fe) {k : Nat} (hk : k < 9) :
    WP isa (.block (selectCand v k)) s fun t =>
      (∀ w < 4, t.gpr (wordReg w) = s.gpr (wordReg w) ||| (feWord v w &&& s.gpr (maskReg k))) ∧
      Keeps [.x9, .x4, .x5, .x6, .x7] s t :=
  WP.mono (selectCandPrefix_ok s v hk 4 (Nat.le_refl _)) fun t ⟨tv, kt⟩ =>
    ⟨fun w hw => by rw [tv w hw]; simp only [hw, ↓reduceIte], kt⟩

/-- The words of `vs[a]` after the candidates `k ≤ n`, zero if `a > n`. -/
def selWord (vs : List Spec.X25519.Fe) (a n w : Nat) : BitVec 64 :=
  if a ≤ n then feWord (vs.getD a 0) w else 0

private theorem or_and_zero (x y : BitVec 64) : x ||| (y &&& 0) = x := by ext i; simp

theorem sel_step (vs : List Spec.X25519.Fe) (a n w : Nat) :
    selWord vs a n w ||| (feWord (vs.getD (n + 1) 0) w &&& mask (decide (a = n + 1))) =
      selWord vs a (n + 1) w := by
  unfold selWord
  by_cases h : a ≤ n
  · simp only [h, ↓reduceIte, show a ≤ n + 1 by omega, show ¬ a = n + 1 by omega, decide_false,
      mask, Bool.false_eq_true]
    exact or_and_zero _ _
  · by_cases he : a = n + 1
    · subst he
      simp only [h, ↓reduceIte, Nat.le_refl, decide_true, mask, BitVec.and_allOnes]
      exact BitVec.zero_or
    · simp only [h, he, ↓reduceIte, show ¬ a ≤ n + 1 by omega, decide_false, mask,
        Bool.false_eq_true]
      exact or_and_zero _ _

theorem selectCands_ok (s : State) {a : Nat}
    (hm : ∀ k, 1 ≤ k → k ≤ 8 → s.gpr (maskReg k) = mask (decide (a = k)))
    (vs : List Spec.X25519.Fe) (n : Nat) (hn : n ≤ 8)
    (h0 : ∀ w < 4, s.gpr (wordReg w) = selWord vs a 0 w) :
    WP isa (.block ((List.range n).flatMap fun k => selectCand (vs.getD (k + 1) 0) (k + 1))) s
      fun t => (∀ w < 4, t.gpr (wordReg w) = selWord vs a n w) ∧ Keeps [.x9, .x4, .x5, .x6, .x7] s t := by
  induction n with
  | zero => exact WP.block_nil ⟨h0, ⟨fun _ _ => rfl, rfl, rfl, rfl, rfl⟩⟩
  | succ n ih =>
    rw [List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil,
      WP.block_append_iff]
    refine WP.mono (ih (by omega)) fun t ⟨tv, kt⟩ => ?_
    have tm : t.gpr (maskReg (n + 1)) = mask (decide (a = n + 1)) := by
      rw [kt.gpr _ (by
        have : ∀ k < 9, maskReg k ∉ [Reg.x9, .x4, .x5, .x6, .x7] := by decide
        exact this (n + 1) (by omega))]
      exact hm (n + 1) (by omega) (by omega)
    refine WP.mono (selectCand_ok t _ (by omega : n + 1 < 9)) fun u ⟨uv, ku⟩ =>
      ⟨fun w hw => ?_, kt.trans ku⟩
    rw [uv w hw, tv w hw, tm, sel_step]

theorem feWord_val (v : Spec.X25519.Fe) :
    val4 (feWord v 0) (feWord v 1) (feWord v 2) (feWord v 3) = v.val := by
  simp only [feWord, Nat.mul_zero, Nat.pow_zero, Nat.div_one, Nat.reduceMul]
  exact limbs_nat _ (by have := v.isLt; simp only [Spec.X25519.P] at this; omega)

private theorem movz0 : (((0 : BitVec 16).setWidth 32).setWidth 64) = 0 := by decide

theorem selectOne_ok (s : State) {a : Nat} (hz : s.gpr .x22 = zeroBit a) :
    WP isa (.block selectOne) s fun t =>
      (∀ w < 4, t.gpr (wordReg w) = if a = 0 then feWord 1 w else 0) ∧ Keeps [.x4, .x5, .x6, .x7] s t := by
  have hf : ∀ w < 4, (if a = 0 then feWord 1 w else 0) =
      [zeroBit a, 0, 0, 0].getD w 0 := by
    intro w hw
    have : w = 0 ∨ w = 1 ∨ w = 2 ∨ w = 3 := by omega
    rcases this with rfl | rfl | rfl | rfl <;> by_cases h : a = 0 <;> simp [h, zeroBit] <;> decide
  apply WP.of_runBlock
  simp only [selectOne, runBlock_cons, runStep_some, runBlock_nil, exec, read_x,
    show (0 : Nat) < 4096 from by decide, show 16 * 0 < Size.w.bits from by decide, ite_true,
    RegUpd.gpr_write, Option.some.injEq, exists_eq_left']
  refine ⟨fun w hw => ?_, ⟨fun r hr => ?_, rfl, rfl, rfl, rfl⟩⟩
  · rw [hf w hw]
    have : w = 0 ∨ w = 1 ∨ w = 2 ∨ w = 3 := by omega
    rcases this with rfl | rfl | rfl | rfl <;>
      simp [wordReg, words, hz, BitVec.setWidth_eq]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2, ite_false]

/-- The field `vs[a]` selected to byte `o`, where `vs[0]` is `1` (`one`) or `0`. -/
theorem selectField_ok {s : State} {base : Addr} (hs : Scr s base) {a : Nat} (ha : a < 9)
    (hm : ∀ k, 1 ≤ k → k ≤ 8 → s.gpr (maskReg k) = mask (decide (a = k)))
    (hz : s.gpr .x22 = zeroBit a) (one : Bool) (vs : List Spec.X25519.Fe)
    (h0 : vs.getD 0 0 = if one then 1 else 0) {o : Nat} (ho : FieldRange o) :
    WP isa (.block (selectField one vs o)) s fun t =>
      F t.mem base o = vs.getD a 0 ∧ Keeps [.x9, .x4, .x5, .x6, .x7] s { t with mem := s.mem } ∧
      Outside base o 32 s.mem t.mem := by
  rw [selectField, List.append_assoc, WP.block_append_iff]
  refine WP.mono (show WP isa (.block (if one then selectOne else zero4)) s fun t =>
      (∀ w < 4, t.gpr (wordReg w) = selWord vs a 0 w) ∧ Keeps [.x9, .x4, .x5, .x6, .x7] s t by
    cases one with
    | true =>
      refine WP.mono (selectOne_ok s hz) fun t ⟨tv, kt⟩ => ⟨fun w hw => ?_, kt.mono (by decide)⟩
      rw [tv w hw, selWord]
      by_cases h : a = 0
      · subst h; simp only [h0, ↓reduceIte, Nat.le_refl]
      · simp only [h, show ¬ a ≤ 0 by omega, ↓reduceIte]
    | false =>
      refine WP.mono (zero4_ok s) fun t ⟨t4, t5, t6, t7, kt⟩ => ⟨fun w hw => ?_, kt.mono (by decide)⟩
      have hw0 : t.gpr (wordReg w) = 0 := by
        have : w = 0 ∨ w = 1 ∨ w = 2 ∨ w = 3 := by omega
        rcases this with rfl | rfl | rfl | rfl
        · exact t4
        · exact t5
        · exact t6
        · exact t7
      rw [hw0, selWord]
      by_cases h : a = 0
      · subst h
        simp only [Bool.false_eq_true, ↓reduceIte] at h0
        simp only [Nat.le_refl, ↓reduceIte, h0]
        simp [feWord]
      · simp only [show ¬ a ≤ 0 by omega, ↓reduceIte]) fun b ⟨bv, kb⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (selectCands_ok b (fun k h1 h8 => by
    rw [kb.gpr _ (by
      have : ∀ k < 9, maskReg k ∉ [Reg.x9, .x4, .x5, .x6, .x7] := by decide
      exact this k (by omega))]
    exact hm k h1 h8) vs 8 (Nat.le_refl _) bv) fun c ⟨cv, kc⟩ => ?_
  have hc : Scr c base := (hs.of_keeps kb (by decide)).of_keeps kc (by decide)
  refine WP.mono (store4_ok hc ho) fun t ht => ?_
  subst t
  have w0 := cv 0 (by decide)
  have w1 := cv 1 (by decide)
  have w2 := cv 2 (by decide)
  have w3 := cv 3 (by decide)
  simp only [wordReg, words, List.getD_cons_zero, List.getD_cons_succ, selWord,
    show a ≤ 8 by omega, ↓reduceIte] at w0 w1 w2 w3
  refine ⟨?_, ?_, ?_⟩
  · rw [F, fe_st4 _ _ (by have := ho.2; omega), w0, w1, w2, w3, feWord_val, toFe_self]
  · have k := kb.trans kc
    exact ⟨k.gpr, rfl, k.rd, k.wr, k.sp⟩
  · rw [kc.mem, kb.mem]
    exact st4_outside _ _ (by have := ho.2; omega) _ _ _ _

/-- The cached point in slots 4–6, with `2Z = 2`. -/
def cachedIn (e : Env) : Spec.Ed25519.Point := ⟨e 4, e 5, e 6, 2⟩

private theorem entries_getD (j a : Nat) (ha : a < 9) (f : Spec.Ed25519.Point → Spec.X25519.Fe) :
    (((List.range 9).map (combCached j)).map f).getD a 0 = f (combCached j a) := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range ha, Option.map_some,
    Option.getD_some]

theorem combCached_T (j a : Nat) : (combCached j a).T = 2 := by
  unfold combCached
  split
  · rfl
  · split; rfl

/-- A field selected to slot `i`, keeping the masks and the other slots. -/
private theorem selectSlot_ok {s : State} {base : Addr} (hs : Scr s base) {a : Nat} (ha : a < 9)
    (hm : ∀ k, 1 ≤ k → k ≤ 8 → s.gpr (maskReg k) = mask (decide (a = k)))
    (hz : s.gpr .x22 = zeroBit a) (one : Bool) (vs : List Spec.X25519.Fe)
    (h0 : vs.getD 0 0 = if one then 1 else 0) (i : Slot) :
    WP isa (.block (selectField one vs (offset i))) s fun t =>
      env t.mem base i = vs.getD a 0 ∧
      (∀ i' : Slot, i' ≠ i → env t.mem base i' = env s.mem base i') ∧ Keep base s t ∧
      (∀ k, 1 ≤ k → k ≤ 8 → t.gpr (maskReg k) = mask (decide (a = k))) ∧ t.gpr .x22 = zeroBit a := by
  refine WP.mono (selectField_ok hs ha hm hz one vs h0 (slot_range i))
    fun t ⟨tv, tk, tm⟩ => ⟨tv, fun i' hi' => ?_, ⟨fun r hr => tk.gpr r (fun h => hr (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with rfl | rfl | rfl | rfl | rfl <;> decide)), tk.rd, tk.wr, tk.sp,
      tm.mono (by simp only [offset]; omega) (by simp only [offset]; omega)⟩,
      fun k h1 h8 => by
        rw [tk.gpr _ (by
          have : ∀ k < 9, maskReg k ∉ [Reg.x9, .x4, .x5, .x6, .x7] := by decide
          exact this k (by omega))]
        exact hm k h1 h8,
      by rw [tk.gpr _ (by decide)]; exact hz⟩
  have hne : i'.val ≠ i.val := fun h => hi' (Fin.ext h)
  exact Outside_F tm (by simp only [offset]; omega) (by simp only [offset]; omega)

theorem combSelect_ok {s : State} {base : Addr} (hs : Scr s base) {a : Nat} (ha : a < 9)
    (hm : ∀ k, 1 ≤ k → k ≤ 8 → s.gpr (maskReg k) = mask (decide (a = k)))
    (hz : s.gpr .x22 = zeroBit a) (j : Nat) :
    WP isa (.block (combSelect j)) s fun t =>
      cachedIn (env t.mem base) = combCached j a ∧ Keep base s t ∧
      (∀ i : Slot, (i.val < 4 ∨ 7 ≤ i.val) → env t.mem base i = env s.mem base i) := by
  rw [combSelect]
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (selectSlot_ok hs ha hm hz true _ (by rw [entries_getD j 0 (by decide)]; rfl) 4)
    fun b ⟨bv, bo, kb, bm, bz⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (selectSlot_ok (kb.scr hs) ha bm bz true _
    (by rw [entries_getD j 0 (by decide)]; rfl) 5) fun c ⟨cv, co, kc, cm, cz⟩ => ?_
  refine WP.mono (selectSlot_ok (kc.scr (kb.scr hs)) ha cm cz false _
    (by rw [entries_getD j 0 (by decide)]; rfl) 6) fun t ⟨tv, tO, kt, _, _⟩ =>
    ⟨?_, (kb.trans kc).trans kt, fun i hi => ?_⟩
  · rw [entries_getD j a ha] at bv cv tv
    have e4 : env t.mem base 4 = env b.mem base 4 := by
      rw [tO 4 (by decide), co 4 (by decide)]
    have e5 : env t.mem base 5 = env c.mem base 5 := tO 5 (by decide)
    simp only [cachedIn, e4, e5, bv, cv, tv, ← combCached_T j a]
  · have ne : ∀ (k : Nat) (h2 : k < 7), 4 ≤ k → i ≠ (⟨k, by omega⟩ : Slot) := fun k _ h1 h => by
      have := congrArg Fin.val h; simp only at this; omega
    rw [tO i (ne 6 (by decide) (by decide)), co i (ne 5 (by decide) (by decide)),
      bo i (ne 4 (by decide) (by decide))]

theorem combSelectFrom_ok (ks : List Nat) (hks : ∀ k ∈ ks, k < 32) {s : State} {base : Addr}
    (hs : Scr s base) {a : Nat} (ha : a < 9)
    (hm : ∀ k, 1 ≤ k → k ≤ 8 → s.gpr (maskReg k) = mask (decide (a = k)))
    (hz : s.gpr .x22 = zeroBit a) {j : Nat} (hj : j ∈ ks) (hj32 : j < 32)
    (hc : s.gpr .x8 = BitVec.ofNat 64 j) :
    WP isa (combSelectFrom ks) s fun t =>
      cachedIn (env t.mem base) = combCached j a ∧ Keep base s t ∧
      (∀ i : Slot, (i.val < 4 ∨ 7 ≤ i.val) → env t.mem base i = env s.mem base i) := by
  induction ks generalizing s with
  | nil => exact absurd hj List.not_mem_nil
  | cons k ks ih =>
    have hk : k < 32 := hks k (by simp)
    have hz' : (BitVec.ofNat 64 j - BitVec.ofNat 64 k == 0) = decide (j = k) := by
      apply Bool.eq_iff_iff.mpr
      simp only [beq_iff_eq, decide_eq_true_eq]
      bv_omega_using [hj32, hk]
    rw [combSelectFrom]
    refine WP.seq (WP.mono (show WP isa (.block [.subImm .x .x9 .x8 k]) s fun t =>
        (t.gpr .x9 == 0) = decide (j = k) ∧ Keeps [.x9] s t by
      apply WP.of_runBlock
      simp only [runBlock_cons, runStep_some, runBlock_nil, exec_subImm_x (show k < 4096 by omega),
        read_x, RegUpd.gpr_write_self, BitVec.setWidth_eq, hc, hz', Option.some.injEq,
        exists_eq_left']
      exact ⟨True.intro, ⟨fun r hr => RegUpd.gpr_write_of_ne _ _ _ (by simpa using hr), rfl, rfl, rfl,
        rfl⟩⟩) fun t ⟨tz, kt⟩ => ?_)
    have ht : Scr t base := hs.of_keeps kt (by decide)
    have tm : ∀ k, 1 ≤ k → k ≤ 8 → t.gpr (maskReg k) = mask (decide (a = k)) := fun k h1 h8 => by
      rw [kt.gpr _ (by
        have : ∀ k < 9, maskReg k ≠ .x9 := by decide
        simpa using this k (by omega))]
      exact hm k h1 h8
    have tzb : t.gpr .x22 = zeroBit a := by rw [kt.gpr _ (by decide)]; exact hz
    have kst : Keep base s t := Keep.of_keeps kt (by decide)
    refine WP.ite (decide (j = k)) (by simp only [eval, read_x, tz]) (fun h => ?_) (fun h => ?_)
    · obtain rfl : j = k := of_decide_eq_true h
      refine WP.mono (combSelect_ok ht ha tm tzb j) fun u ⟨uv, ku, ue⟩ =>
        ⟨uv, kst.trans ku, fun i hi => by rw [ue i hi, kt.mem]⟩
    · have hne : j ≠ k := of_decide_eq_false h
      have hj' : j ∈ ks := by
        rcases List.mem_cons.mp hj with h | h
        · exact absurd h hne
        · exact h
      refine WP.mono (ih (fun k hk => hks k (List.mem_cons_of_mem _ hk)) ht tm tzb hj'
        (by rw [kt.gpr _ (by decide)]; exact hc)) fun u ⟨uv, ku, ue⟩ =>
        ⟨uv, kst.trans ku, fun i hi => by rw [ue i hi, kt.mem]⟩

end VG.Proof.Ed25519.AArch64
