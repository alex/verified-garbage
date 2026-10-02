import VerifiedGarbage.Proof.Ed25519.AArch64.CombDigit
import VerifiedGarbage.Proof.Ed25519.AArch64.Field
import VerifiedGarbage.Proof.Ed25519.AArch64.CounterKeep

/-!
# The comb's constant-time selection, for two digits at once

Untrusted. With `oddReg k` (`evenReg k`) all ones exactly for `k` the odd
(even) digit's magnitude, and `x22` (`x8`) the bit of a zero magnitude,
`selectWord` builds every candidate's word once, ANDs it with both digits'
masks and ORs it into `x4` and `x5`, so only each digit's candidate
survives, and stores them.
-/

namespace VG.Proof.Ed25519.AArch64

open VG VG.AArch64 VG.Impl.Ed25519 VG.Impl.Ed25519.AArch64 VG.Proof.Ed25519 VG.Proof.X25519
open Word64

private theorem odd_regs : ∀ k < 9, oddReg k ∉ [Reg.x9, .x2, .x4, .x5] := by decide
private theorem even_regs : ∀ k < 9, evenReg k ∉ [Reg.x9, .x2, .x4, .x5] := by decide

private theorem ne_of_not_mem {r : Reg} {rs : List Reg} (h : r ∉ rs) {r' : Reg} (hr : r' ∈ rs) :
    r ≠ r' := fun e => h (e ▸ hr)

theorem selectCand_ok (s : State) (v : Spec.X25519.Fe) {k : Nat} (hk : k < 9) (w : Nat) :
    WP isa (.block (selectCand v k w)) s fun t =>
      t.gpr .x4 = s.gpr .x4 ||| (feWord v w &&& s.gpr (oddReg k)) ∧
      t.gpr .x5 = s.gpr .x5 ||| (feWord v w &&& s.gpr (evenReg k)) ∧
      Keeps [.x9, .x2, .x4, .x5] s t := by
  have ho := odd_regs k hk
  have he := even_regs k hk
  have ho9 := ne_of_not_mem ho (r' := .x9) (by decide)
  have he9 := ne_of_not_mem he (r' := .x9) (by decide)
  have he2 := ne_of_not_mem he (r' := .x2) (by decide)
  have he4 := ne_of_not_mem he (r' := .x4) (by decide)
  rw [selectCand, WP.block_append_iff]
  refine WP.mono (const64_ok s .x9 (feWord v w)) fun a ⟨a9, ka⟩ => ?_
  have am : a.gpr (oddReg k) = s.gpr (oddReg k) := ka.gpr _ (by simpa using ho9)
  have ae : a.gpr (evenReg k) = s.gpr (evenReg k) := ka.gpr _ (by simpa using he9)
  have a4 : a.gpr .x4 = s.gpr .x4 := ka.gpr _ (by decide)
  have a5 : a.gpr .x5 = s.gpr .x5 := ka.gpr _ (by decide)
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, read_x, RegUpd.gpr_write,
    BitVec.setWidth_eq, he2, he4, ite_true, ite_false, reduceCtorEq, a9, am, ae, a4, a5,
    Option.some.injEq, exists_eq_left']
  refine ⟨True.intro, True.intro, ⟨fun r hr => ?_, ka.mem, ka.rd, ka.wr, ka.sp⟩⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [RegUpd.gpr_write, hr.2.1, hr.2.2.1, hr.2.2.2, ite_false]
  exact ka.gpr _ (by simpa using hr.1)

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

/-- The masks of both digits, for the magnitudes `ao` and `ae`. -/
def Masks (ao ae : Nat) (s : State) : Prop :=
  (∀ k, 1 ≤ k → k ≤ 8 → s.gpr (oddReg k) = mask (decide (ao = k))) ∧
  (∀ k, 1 ≤ k → k ≤ 8 → s.gpr (evenReg k) = mask (decide (ae = k))) ∧
  s.gpr .x22 = zeroBit ao ∧ s.gpr .x8 = zeroBit ae

theorem Masks.of_keeps {ao ae : Nat} {s t : State} (h : Masks ao ae s)
    (k : Keeps [.x9, .x2, .x4, .x5] s t) : Masks ao ae t := by
  refine ⟨fun j h1 h8 => ?_, fun j h1 h8 => ?_, by rw [k.gpr _ (by decide)]; exact h.2.2.1,
    by rw [k.gpr _ (by decide)]; exact h.2.2.2⟩
  · rw [k.gpr _ (odd_regs j (by omega))]; exact h.1 j h1 h8
  · rw [k.gpr _ (even_regs j (by omega))]; exact h.2.1 j h1 h8

theorem selectCands_ok (s : State) {ao ae : Nat} (hm : Masks ao ae s)
    (vs : List Spec.X25519.Fe) (w n : Nat) (hn : n ≤ 8)
    (h0 : s.gpr .x4 = selWord vs ao 0 w ∧ s.gpr .x5 = selWord vs ae 0 w) :
    WP isa (.block ((List.range n).flatMap fun k => selectCand (vs.getD (k + 1) 0) (k + 1) w)) s
      fun t => t.gpr .x4 = selWord vs ao n w ∧ t.gpr .x5 = selWord vs ae n w ∧
        Keeps [.x9, .x2, .x4, .x5] s t := by
  induction n with
  | zero => exact WP.block_nil ⟨h0.1, h0.2, ⟨fun _ _ => rfl, rfl, rfl, rfl, rfl⟩⟩
  | succ n ih =>
    rw [List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil,
      WP.block_append_iff]
    refine WP.mono (ih (by omega)) fun t ⟨t4, t5, kt⟩ => ?_
    have tm := hm.of_keeps kt
    refine WP.mono (selectCand_ok t _ (by omega : n + 1 < 9) w) fun u ⟨u4, u5, ku⟩ =>
      ⟨?_, ?_, kt.trans ku⟩
    · rw [u4, t4, tm.1 (n + 1) (by omega) (by omega), sel_step]
    · rw [u5, t5, tm.2.1 (n + 1) (by omega) (by omega), sel_step]

private theorem movz0 : (((0 : BitVec 16).setWidth 32).setWidth 64) = 0 := by decide

theorem selectStart_ok (s : State) {ao ae : Nat} (hm : Masks ao ae s) (one : Bool)
    (vs : List Spec.X25519.Fe) (h0 : vs.getD 0 0 = if one then 1 else 0) (w : Nat) (hw : w < 4) :
    WP isa (.block (selectStart one w)) s fun t =>
      t.gpr .x4 = selWord vs ao 0 w ∧ t.gpr .x5 = selWord vs ae 0 w ∧
        Keeps [.x9, .x2, .x4, .x5] s t := by
  have hz : ∀ a, (if (one && w == 0) = true then zeroBit a else 0) = selWord vs a 0 w := fun a => by
    unfold selWord zeroBit
    by_cases ha : a = 0
    · subst ha
      have : w = 0 ∨ w = 1 ∨ w = 2 ∨ w = 3 := by omega
      simp only [Nat.le_refl, ↓reduceIte, h0]
      cases one <;> rcases this with rfl | rfl | rfl | rfl <;> decide
    · simp [ha, show ¬ a ≤ 0 by omega]
  rw [← hz ao, ← hz ae]
  unfold selectStart
  by_cases h : (one && w == 0) = true
  · simp only [h, ↓reduceIte]
    apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec_addImm_x (show 0 < 4096 by decide),
      read_x, RegUpd.gpr_write, BitVec.setWidth_eq, BitVec.add_zero, ite_true, ite_false, reduceCtorEq,
      hm.2.2.1, hm.2.2.2, Option.some.injEq, exists_eq_left']
    refine ⟨True.intro, True.intro, ⟨fun r hr => ?_, rfl, rfl, rfl, rfl⟩⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, hr.2.2.1, hr.2.2.2, ite_false]
  · simp only [h, ↓reduceIte, Bool.false_eq_true]
    apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec,
      show 16 * 0 < Size.w.bits from by decide, ite_true, RegUpd.gpr_write, ite_false, reduceCtorEq,
      Nat.mul_zero, BitVec.shiftLeft_zero, movz0, Option.some.injEq, exists_eq_left']
    refine ⟨True.intro, True.intro, ⟨fun r hr => ?_, rfl, rfl, rfl, rfl⟩⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, hr.2.2.1, hr.2.2.2, ite_false]

/-- `m'` agrees with `m` but on the `n` bytes at offsets `o` and `e` of `base`. -/
def Frame2 (base : Addr) (o e n : Nat) (m m' : Mem) : Prop :=
  ∀ x, (ofs base x < o ∨ o + n ≤ ofs base x) → (ofs base x < e ∨ e + n ≤ ofs base x) → m' x = m x

theorem Frame2.trans {base : Addr} {o e n : Nat} {m₁ m₂ m₃ : Mem} (h : Frame2 base o e n m₁ m₂)
    (k : Frame2 base o e n m₂ m₃) : Frame2 base o e n m₁ m₃ :=
  fun x h1 h2 => (k x h1 h2).trans (h x h1 h2)

theorem Frame2.mono {base : Addr} {o e n o' e' n' : Nat} {m m' : Mem} (h : Frame2 base o e n m m')
    (h1 : o' ≤ o) (h2 : o + n ≤ o' + n') (h3 : e' ≤ e) (h4 : e + n ≤ e' + n') :
    Frame2 base o' e' n' m m' := fun x a b => h x (by omega) (by omega)

theorem Frame2.word {base : Addr} {o e n : Nat} {m m' : Mem} (h : Frame2 base o e n m m') {d : Nat}
    (h1 : d + 8 ≤ o ∨ o + n ≤ d) (h2 : d + 8 ≤ e ∨ e + n ≤ d) (hd : d + 8 < 2 ^ 64) :
    word m' base d = word m base d :=
  (Mem.readW_congr fun i hi => (h _ (by rw [ofs_off base (by omega)]; omega)
    (by rw [ofs_off base (by omega)]; omega)).symm).symm

theorem Frame2.F {base : Addr} {o e n : Nat} {m m' : Mem} (h : Frame2 base o e n m m') {d : Nat}
    (h1 : d + 32 ≤ o ∨ o + n ≤ d) (h2 : d + 32 ≤ e ∨ e + n ≤ d) (hd : d + 32 < 2 ^ 64) :
    F m' base d = F m base d := by
  change toFe (AArch64.fe m' base d) = toFe (AArch64.fe m base d)
  unfold AArch64.fe
  rw [h.word (by omega) (by omega) (by omega), h.word (by omega) (by omega) (by omega),
    h.word (by omega) (by omega) (by omega), h.word (by omega) (by omega) (by omega)]

/-- What a selection leaves of the registers. -/
def RegsKept (s t : State) : Prop :=
  (∀ r, r ∉ [Reg.x9, .x2, .x4, .x5] → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp

theorem RegsKept.trans {s t u : State} (h : RegsKept s t) (k : RegsKept t u) : RegsKept s u :=
  ⟨fun r hr => (k.1 r hr).trans (h.1 r hr), k.2.1.trans h.2.1, k.2.2.1.trans h.2.2.1,
    k.2.2.2.trans h.2.2.2⟩

theorem RegsKept.of_keeps {s t : State} (k : Keeps [.x9, .x2, .x4, .x5] s t) : RegsKept s t :=
  ⟨k.gpr, k.rd, k.wr, k.sp⟩

theorem Masks.of_kept {ao ae : Nat} {s t : State} (h : Masks ao ae s) (k : RegsKept s t) :
    Masks ao ae t := by
  refine ⟨fun j h1 h8 => ?_, fun j h1 h8 => ?_, by rw [k.1 _ (by decide)]; exact h.2.2.1,
    by rw [k.1 _ (by decide)]; exact h.2.2.2⟩
  · rw [k.1 _ (odd_regs j (by omega))]; exact h.1 j h1 h8
  · rw [k.1 _ (even_regs j (by omega))]; exact h.2.1 j h1 h8

theorem selectWord_ok {s : State} {base : Addr} (hs : Scr s base) {ao ae : Nat} (hm : Masks ao ae s)
    (one : Bool) (vs : List Spec.X25519.Fe) (h0 : vs.getD 0 0 = if one then 1 else 0)
    {o e : Nat} (ho : o % 8 = 0) (he : e % 8 = 0)
    (hb : o + 32 ≤ 8192) (hbe : e + 32 ≤ 8192) (w : Nat) (hw : w < 4) :
    WP isa (.block (selectWord one vs o e w)) s fun t =>
      t.mem = (s.mem.writeW (off base (o + 8 * w)) (selWord vs ao 8 w)).writeW (off base (e + 8 * w))
        (selWord vs ae 8 w) ∧ RegsKept s t := by
  have _hcap : workSize true = 8192 := rfl
  rw [selectWord, List.append_assoc, WP.block_append_iff]
  refine WP.mono (selectStart_ok s hm one vs h0 w hw) fun a ⟨a4, a5, ka⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (selectCands_ok a (hm.of_keeps ka) vs w 8 (le_refl _) ⟨a4, a5⟩)
    fun b ⟨b4, b5, kb⟩ => ?_
  have hsb : Scr b base := (hs.of_keeps ka (by decide)).of_keeps kb (by decide)
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil,
    store_sc hsb (show (o + 8 * w) % 8 = 0 by omega) (by omega),
    store_sc (hsb.setMem _) (show (e + 8 * w) % 8 = 0 by omega) (by omega),
    Option.some.injEq, exists_eq_left', b4, b5]
  exact ⟨by rw [kb.mem, ka.mem], (RegsKept.of_keeps ka).trans ⟨kb.gpr, kb.rd, kb.wr, kb.sp⟩⟩

theorem selectFieldPrefix_ok {s : State} {base : Addr} (hs : Scr s base) {ao ae : Nat}
    (hm : Masks ao ae s) (one : Bool) (vs : List Spec.X25519.Fe)
    (h0 : vs.getD 0 0 = if one then 1 else 0)
    {o e : Nat} (ho : o % 8 = 0) (he : e % 8 = 0) (hoe : o + 32 ≤ e ∨ e + 32 ≤ o)
    (hb : o + 32 ≤ 8192) (hbe : e + 32 ≤ 8192) (n : Nat) (hn : n ≤ 4) :
    WP isa (.block ((List.range n).flatMap fun w => selectWord one vs o e w)) s fun t =>
      (∀ w < n, word t.mem base (o + 8 * w) = selWord vs ao 8 w ∧
        word t.mem base (e + 8 * w) = selWord vs ae 8 w) ∧
      Frame2 base o e 32 s.mem t.mem ∧ RegsKept s t := by
  induction n with
  | zero => exact WP.block_nil ⟨fun w hw => absurd hw (Nat.not_lt_zero _), fun _ _ _ => rfl,
      fun _ _ => rfl, rfl, rfl, rfl⟩
  | succ n ih =>
    rw [List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil,
      WP.block_append_iff]
    refine WP.mono (ih (by omega)) fun t ⟨tv, tf, kt⟩ => ?_
    have ht : Scr t base := ⟨(kt.1 _ (by decide)).trans hs.x0, kt.2.2.1 ▸ hs.wr, hs.nowrap⟩
    refine WP.mono (selectWord_ok ht (hm.of_kept kt) one vs h0 ho he hb hbe n (by omega))
      fun u ⟨um, ku⟩ => ⟨fun w hw => ?_, ?_, kt.trans ku⟩
    · rw [um]
      by_cases hwn : w = n
      · subst hwn
        refine ⟨?_, word_writeW_self _ _ _ _⟩
        rw [word_writeW_sep _ _ _ (by omega) (by omega) (by omega), word_writeW_self]
      · have hwl : w < n := by omega
        rw [word_writeW_sep _ _ _ (by omega) (by omega) (by omega),
          word_writeW_sep _ _ _ (by omega) (by omega) (by omega),
          word_writeW_sep _ _ _ (by omega) (by omega) (by omega),
          word_writeW_sep _ _ _ (by omega) (by omega) (by omega)]
        exact tv w hwl
    · rw [um]
      refine tf.trans fun x h1 h2 => ?_
      rw [write_outside _ _ _ (by omega) (by omega) (by omega) h2,
        write_outside _ _ _ (by omega) (by omega) (by omega) h1]

theorem feWord_val (v : Spec.X25519.Fe) :
    val4 (feWord v 0) (feWord v 1) (feWord v 2) (feWord v 3) = v.val := by
  simp only [feWord, Nat.mul_zero, Nat.pow_zero, Nat.div_one, Nat.reduceMul]
  exact limbs_nat _ (by have := v.isLt; simp only [Spec.X25519.P] at this; omega)

theorem selectField_ok {s : State} {base : Addr} (hs : Scr s base) {ao ae : Nat} (hao : ao < 9)
    (hae : ae < 9) (hm : Masks ao ae s) (one : Bool) (vs : List Spec.X25519.Fe)
    (h0 : vs.getD 0 0 = if one then 1 else 0)
    {o e : Nat} (ho : o % 8 = 0) (he : e % 8 = 0) (hoe : o + 32 ≤ e ∨ e + 32 ≤ o)
    (hb : o + 32 ≤ 8192) (hbe : e + 32 ≤ 8192) :
    WP isa (.block (selectField one vs o e)) s fun t =>
      F t.mem base o = vs.getD ao 0 ∧ F t.mem base e = vs.getD ae 0 ∧
      Frame2 base o e 32 s.mem t.mem ∧ RegsKept s t := by
  refine WP.mono (selectFieldPrefix_ok hs hm one vs h0 ho he hoe hb hbe 4 (le_refl _))
    fun t ⟨tv, tf, kt⟩ => ⟨?_, ?_, tf, kt⟩
  · simp only [F, fe]
    have w0 := (tv 0 (by decide)).1
    have w1 := (tv 1 (by decide)).1
    have w2 := (tv 2 (by decide)).1
    have w3 := (tv 3 (by decide)).1
    simp only [Nat.mul_zero, Nat.add_zero, Nat.mul_one, Nat.reduceMul] at w0 w1 w2 w3
    rw [w0, w1, w2, w3]
    simp only [selWord, show ao ≤ 8 by omega, ↓reduceIte]
    rw [feWord_val, toFe_self]
  · simp only [F, fe]
    have w0 := (tv 0 (by decide)).2
    have w1 := (tv 1 (by decide)).2
    have w2 := (tv 2 (by decide)).2
    have w3 := (tv 3 (by decide)).2
    simp only [Nat.mul_zero, Nat.add_zero, Nat.mul_one, Nat.reduceMul] at w0 w1 w2 w3
    rw [w0, w1, w2, w3]
    simp only [selWord, show ae ≤ 8 by omega, ↓reduceIte]
    rw [feWord_val, toFe_self]

/-- The cached point in slots `a`, `b`, `c`, with `2Z = 2`. -/
def cachedAt (e : Env) (a b c : Slot) : Spec.Ed25519.Point := ⟨e a, e b, e c, 2⟩

private theorem entries_getD (j a : Nat) (ha : a < 9) (f : Spec.Ed25519.Point → Spec.X25519.Fe) :
    (((List.range 9).map (combCached j)).map f).getD a 0 = f (combCached j a) := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range ha, Option.map_some,
    Option.getD_some]

theorem combCached_T (j a : Nat) : (combCached j a).T = 2 := by
  unfold combCached
  split
  · rfl
  · split; rfl

theorem cachedAt_eq {e : Env} {a b c : Slot} {q : Spec.Ed25519.Point} (hq : q.T = 2)
    (ha : e a = q.X) (hb : e b = q.Y) (hc : e c = q.Z) : cachedAt e a b c = q := by
  cases q
  simp only [cachedAt, ha, hb, hc] at hq ⊢
  rw [hq]

theorem combSelect_ok {s : State} {base : Addr} (hs : Scr s base) {ao ae : Nat} (hao : ao < 9)
    (hae : ae < 9) (hm : Masks ao ae s) (j : Nat) :
    WP isa (.block (combSelect j)) s fun t =>
      cachedAt (env t.mem base) 4 5 6 = combCached j ao ∧
      cachedAt (env t.mem base) 13 14 15 = combCached j ae ∧
      Frame2 base (offset 4) (offset 13) 96 s.mem t.mem ∧ RegsKept s t := by
  rw [combSelect]
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (selectField_ok hs hao hae hm true _ (by rw [entries_getD j 0 (by decide)]; rfl)
    (o := offset 4) (e := offset 13) (by decide) (by decide) (by decide) (by decide) (by decide))
    fun b ⟨b4, b13, bf, kb⟩ => ?_
  have hsb : Scr b base := ⟨(kb.1 _ (by decide)).trans hs.x0, kb.2.2.1 ▸ hs.wr, hs.nowrap⟩
  rw [WP.block_append_iff]
  refine WP.mono (selectField_ok hsb hao hae (hm.of_kept kb) true _
    (by rw [entries_getD j 0 (by decide)]; rfl)
    (o := offset 5) (e := offset 14) (by decide) (by decide) (by decide) (by decide) (by decide))
    fun c ⟨c5, c14, cf, kc⟩ => ?_
  have hsc : Scr c base := ⟨(kc.1 _ (by decide)).trans hsb.x0, kc.2.2.1 ▸ hsb.wr, hs.nowrap⟩
  refine WP.mono (selectField_ok hsc hao hae ((hm.of_kept kb).of_kept kc) false _
    (by rw [entries_getD j 0 (by decide)]; rfl)
    (o := offset 6) (e := offset 15) (by decide) (by decide) (by decide) (by decide) (by decide))
    fun t ⟨t6, t15, tf, kt⟩ => ⟨?_, ?_, ?_, (kb.trans kc).trans kt⟩
  · rw [entries_getD j ao hao] at b4 c5 t6
    refine cachedAt_eq (combCached_T j ao) ?_ ?_ t6
    · change F t.mem base (offset 4) = _
      rw [tf.F (by decide) (by decide) (by decide), cf.F (by decide) (by decide) (by decide), b4]
    · change F t.mem base (offset 5) = _
      rw [tf.F (by decide) (by decide) (by decide), c5]
  · rw [entries_getD j ae hae] at b13 c14 t15
    refine cachedAt_eq (combCached_T j ae) ?_ ?_ t15
    · change F t.mem base (offset 13) = _
      rw [tf.F (by decide) (by decide) (by decide), cf.F (by decide) (by decide) (by decide), b13]
    · change F t.mem base (offset 14) = _
      rw [tf.F (by decide) (by decide) (by decide), c14]
  · exact ((bf.mono (by decide) (by decide) (by decide) (by decide)).trans
      (cf.mono (by decide) (by decide) (by decide) (by decide))).trans
      (tf.mono (by decide) (by decide) (by decide) (by decide))

theorem combSelectFrom_ok (ks : List Nat) (hks : ∀ k ∈ ks, k < 32) {s : State} {base : Addr}
    (hs : Scr s base) {ao ae : Nat} (hao : ao < 9) (hae : ae < 9) (hm : Masks ao ae s)
    {j : Nat} (hj : j ∈ ks) (hj32 : j < 32) (hc : s.gpr .x19 = BitVec.ofNat 64 j) :
    WP isa (combSelectFrom ks) s fun t =>
      cachedAt (env t.mem base) 4 5 6 = combCached j ao ∧
      cachedAt (env t.mem base) 13 14 15 = combCached j ae ∧
      Frame2 base (offset 4) (offset 13) 96 s.mem t.mem ∧ RegsKept s t := by
  induction ks generalizing s with
  | nil => exact absurd hj List.not_mem_nil
  | cons k ks ih =>
    have hk : k < 32 := hks k (by simp)
    have hz' : (BitVec.ofNat 64 j - BitVec.ofNat 64 k == 0) = decide (j = k) := by
      apply Bool.eq_iff_iff.mpr
      simp only [beq_iff_eq, decide_eq_true_eq]
      bv_omega_using [hj32, hk]
    rw [combSelectFrom]
    refine WP.seq (WP.mono (show WP isa (.block [.subImm .x .x9 .x19 k]) s fun t =>
        (t.gpr .x9 == 0) = decide (j = k) ∧ Keeps [.x9] s t by
      apply WP.of_runBlock
      simp only [runBlock_cons, runStep_some, runBlock_nil, exec_subImm_x (show k < 4096 by omega),
        read_x, RegUpd.gpr_write_self, BitVec.setWidth_eq, hc, hz', Option.some.injEq,
        exists_eq_left']
      exact ⟨True.intro, ⟨fun r hr => RegUpd.gpr_write_of_ne _ _ _ (by simpa using hr), rfl, rfl, rfl,
        rfl⟩⟩) fun t ⟨tz, kt⟩ => ?_)
    have ht : Scr t base := hs.of_keeps kt (by decide)
    have kst : RegsKept s t := RegsKept.of_keeps (kt.mono (by decide))
    have tm : Masks ao ae t := hm.of_kept kst
    refine WP.ite (decide (j = k)) (by simp only [eval, read_x, tz]) (fun h => ?_) (fun h => ?_)
    · obtain rfl : j = k := of_decide_eq_true h
      refine WP.mono (combSelect_ok ht hao hae tm j) fun u ⟨u1, u2, uf, ku⟩ =>
        ⟨u1, u2, by rw [← kt.mem]; exact uf, kst.trans ku⟩
    · have hne : j ≠ k := of_decide_eq_false h
      have hj' : j ∈ ks := by
        rcases List.mem_cons.mp hj with h | h
        · exact absurd h hne
        · exact h
      refine WP.mono (ih (fun k hk => hks k (List.mem_cons_of_mem _ hk)) ht tm hj'
        (by rw [kt.gpr _ (by decide)]; exact hc)) fun u ⟨u1, u2, uf, ku⟩ =>
        ⟨u1, u2, by rw [← kt.mem]; exact uf, kst.trans ku⟩

end VG.Proof.Ed25519.AArch64
