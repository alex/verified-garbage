import VerifiedGarbage.Proof.Weierstrass.X86_64.Copy
import VerifiedGarbage.Proof.Mont.X86_64.Ops
import VerifiedGarbage.Impl.Ecdsa.X86_64

/-!
# ECDSA on x86-64: the masks of the checks, and the flag

The checks of `Impl/Ecdsa/X86_64.lean` as masks, all ones or zero:
`nonzero a` sets `rdx` to all ones iff `[a] ≠ 0` (`nonzero_ok`), `ltN a` sets
`rax` to all ones iff `[a] < [MN]` (`ltN_ok`), and `andFlag` ands `rdx` into
the flag word (`andFlag_ok`); so `checkRange a` ands the mask of
`0 < [a] < [MN]` into the flag (`checkRange_ok`) and `checkNonzero a` the mask
of `[a] ≠ 0` (`checkNonzero_ok`).
-/

namespace VG.Proof.Weierstrass.X86_64

open VG VG.X86_64 VG.Impl.Mont.X86_64 VG.Impl.Ecdsa.X86_64 VG.Proof.Mont.X86_64
open VG.Proof.X25519.X86_64 (Keeps Keeps.trans Keeps.mono sub_borrow sbb_borrow)

/-- A mask: all ones if `p`, else zero. -/
abbrev mask (p : Prop) [Decidable p] : BitVec 64 := if p then BitVec.allOnes 64 else 0

theorem mask_and (p q : Prop) [Decidable p] [Decidable q] : mask p &&& mask q = mask (p ∧ q) := by
  by_cases hp : p <;> by_cases hq : q <;>
    simp only [mask, hp, hq, ite_true, ite_false, and_self, and_false, false_and] <;> decide

theorem or_eq_zero (x y : BitVec 64) : x ||| y = 0 ↔ x = 0 ∧ y = 0 := BitVec.or_eq_zero_iff

/-! ## Nonzero -/

/-- The `or`s of `nonzero`. -/
theorem ors_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {a : Nat} :
    ∀ k, a + 8 * (k + 1) ≤ size →
    WP isa (.block ((List.range k).map fun j => .alu .or .rdx (.mem (sc (a + 8 * (j + 1)))))) s fun s' =>
      (s'.gpr .rdx = 0 ↔ s.gpr .rdx = 0 ∧ ∀ j < k, word s.mem base (a + 8 * (j + 1)) = 0) ∧
      Keeps [.rdx] s s'
  | 0, _ => WP.block_nil ⟨⟨fun h => ⟨h, fun _ hj => absurd hj (Nat.not_lt_zero _)⟩, fun h => h.1⟩,
      fun _ _ => rfl, rfl, rfl, rfl⟩
  | k + 1, hk => by
    rw [List.range_succ, List.map_append, List.map_cons, List.map_nil, WP.block_append_iff]
    refine WP.mono (ors_ok hs k (by omega)) fun s₁ ⟨e₁, k₁⟩ => ?_
    have hs₁ := hs.of_keeps k₁ (by decide)
    apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc_sc hs₁ (d := a + 8 * (k + 1))
      (by omega), Option.bind_some, RegUpd.gpr_setReg, ite_true, Option.some.injEq, exists_eq_left',
      or_eq_zero, e₁, k₁.2.1]
    refine ⟨⟨fun ⟨⟨h₀, h⟩, hw⟩ => ⟨h₀, fun j hj => ?_⟩, fun ⟨h₀, h⟩ => ⟨⟨h₀, fun j hj => h j (by omega)⟩,
      h k (by omega)⟩⟩, fun r hr => ?_, ?_, ?_, ?_⟩
    · rcases Nat.lt_or_ge j k with hj' | hj'
      · exact h j hj'
      · obtain rfl : j = k := by omega
        exact hw
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rw [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, ite_eq_right hr, k₁.1 r (by simpa using hr)]
    · rw [RegUpd.mem_setReg, RegUpd.mem_arithFlags, k₁.2.1]
    · rw [RegUpd.rd_setReg, RegUpd.rd_arithFlags, k₁.2.2.1]
    · rw [RegUpd.wr_setReg, RegUpd.wr_arithFlags, k₁.2.2.2]

theorem sbb_self (x : BitVec 64) (b : Bool) :
    x - x - (BitVec.ofBool b).setWidth 64 = if b then BitVec.allOnes 64 else 0 := by
  rw [BitVec.sub_self]; cases b <;> decide

/-- `rdx` is all ones iff `[a] ≠ 0`; `rcx` changes too. -/
theorem nonzero_ok (c : Cfg) {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {a : Nat}
    (hn : 0 < c.n) (ha : a + 8 * c.n ≤ size) :
    WP isa (.block (c.nonzero a)) s fun s' =>
      s'.gpr .rdx = mask (wordsVal s.mem base a c.n ≠ 0) ∧ Keeps [.rcx, .rdx] s s' := by
  rw [Cfg.nonzero, List.append_assoc, WP.block_append_iff]
  refine WP.mono (show WP isa (.block [.mov .rdx (.mem (sc a))]) s (fun s₁ =>
      s₁.gpr .rdx = word s.mem base a ∧ Keeps [.rdx] s s₁) by
    apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc_sc hs (d := a) (by omega),
      Option.map_some, RegUpd.gpr_setReg, ite_true, Option.some.injEq, exists_eq_left']
    refine ⟨trivial, fun r hr => ?_, rfl, rfl, rfl⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    simp only [RegUpd.gpr_setReg, hr, ite_false]) fun s₁ ⟨e₁, k₁⟩ => ?_
  have hs₁ := hs.of_keeps k₁ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (ors_ok hs₁ (a := a) (c.n - 1) (by omega)) fun s₂ ⟨e₂, k₂⟩ => ?_
  rw [e₁, k₁.2.1] at e₂
  have hz : s₂.gpr .rdx = 0 ↔ wordsVal s.mem base a c.n = 0 := by
    rw [e₂, wordsVal_eq_zero_iff]
    constructor
    · intro ⟨h₀, h⟩ j hj
      rcases j with _ | j
      · simpa using h₀
      · exact h j (by omega)
    · intro h
      exact ⟨by simpa using h 0 hn, fun j hj => h (j + 1) (by omega)⟩
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, readSrc32, State.setReg32,
    Option.map_some, Option.bind_some, RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, RegUpd.cf_arithFlags,
    RegUpd.cf_setReg, ite_true, ite_false, reduceCtorEq, Option.some.injEq, exists_eq_left', sbb_self]
  refine ⟨?_, fun r hr => ?_, ?_, ?_, ?_⟩
  · have h0 : (BitVec.setWidth 64 (0 : BitVec 32)).toNat = 0 := rfl
    rw [h0]
    by_cases h : wordsVal s.mem base a c.n = 0
    · have := hz.mpr h
      rw [this]
      simp only [h, mask, ne_eq, not_true_eq_false, ite_false]
      rfl
    · have : s₂.gpr .rdx ≠ 0 := fun h' => h (hz.mp h')
      have : 0 < (s₂.gpr .rdx).toNat := Nat.pos_of_ne_zero fun h' => this (BitVec.eq_of_toNat_eq h')
      simp only [this, decide_true, ite_true, mask, ne_eq, h, not_false_eq_true]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, ite_eq_right hr.2, RegUpd.gpr_setReg, RegUpd.gpr_arithFlags,
      ite_eq_right hr.1, RegUpd.gpr_setReg, ite_eq_right hr.1, k₂.1 r (by simpa using hr.2),
      k₁.1 r (by simpa using hr.2)]
  · simp only [RegUpd.mem_setReg, RegUpd.mem_arithFlags, k₂.2.1, k₁.2.1]
  · simp only [RegUpd.rd_setReg, RegUpd.rd_arithFlags, k₂.2.2.1, k₁.2.2.1]
  · simp only [RegUpd.wr_setReg, RegUpd.wr_arithFlags, k₂.2.2.2, k₁.2.2.2]

/-! ## Comparison with `n` -/

/-- One word of `ltN`'s subtraction. -/
def ltStep (a m j : Nat) : List Instr :=
  [.mov .rdx (.mem (sc (a + 8 * j))), .alu (if j = 0 then .sub else .sbb) .rdx (.mem (sc (m + 8 * j)))]

theorem ltStep_zero (a m : Nat) :
    ltStep a m 0 = [.mov .rdx (.mem (sc (a + 8 * 0))), .alu .sub .rdx (.mem (sc (m + 8 * 0)))] := rfl

theorem ltStep_succ (a m k : Nat) :
    ltStep a m (k + 1) =
      [.mov .rdx (.mem (sc (a + 8 * (k + 1)))), .alu .sbb .rdx (.mem (sc (m + 8 * (k + 1))))] := rfl

theorem ltN_eq (c : Cfg) (a : Nat) :
    c.ltN a = (List.range c.n).flatMap (ltStep a (c.sl MN)) ++ ([.alu .sbb .rax (.reg .rax)] : List Instr) := rfl

/-- The borrow out of `A' = A + P a` less `M' = M + P b`, for `A, M < P`. -/
theorem lt_top {A M P x y : Nat} (hA : A < P) (hM : M < P) :
    (A + P * x < M + P * y) ↔ x < y + (decide (A < M)).toNat := by
  rcases Nat.lt_trichotomy x y with h | rfl | h
  · have := Nat.mul_le_mul_left P (show x + 1 ≤ y by omega)
    rw [Nat.mul_succ] at this
    constructor
    · intro; omega
    · intro; omega
  · by_cases h : A < M <;> simp only [h, decide_true, decide_false, Bool.toNat_true, Bool.toNat_false] <;> omega
  · have := Nat.mul_le_mul_left P (show y + 1 ≤ x by omega)
    rw [Nat.mul_succ] at this
    have := Bool.toNat_le (decide (A < M))
    constructor
    · intro; omega
    · intro; omega

theorem ltSteps_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {a m : Nat} :
    ∀ k, a + 8 * (k + 1) ≤ size → m + 8 * (k + 1) ≤ size →
    WP isa (.block ((List.range (k + 1)).flatMap (ltStep a m))) s fun s' =>
      s'.cf = some (decide (wordsVal s.mem base a (k + 1) < wordsVal s.mem base m (k + 1))) ∧
      Keeps [.rdx] s s'
  | 0, ha, hm => by
    apply WP.of_runBlock
    rw [show (List.range (0 + 1)).flatMap (ltStep a m) = ltStep a m 0 from rfl, ltStep_zero]
    simp only [runBlock_cons, runStep_some,
      runBlock_nil, exec, execAlu, readSrc, ld_sc hs (d := a + 8 * 0) (by omega), Option.map_some,
      Option.bind_some, RegUpd.gpr_setReg, ite_true, RegUpd.mem_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg,
      State.load64, ea_sc, hs.rdi, ld_sc hs (d := m + 8 * 0) (by omega), RegUpd.cf_setReg,
      RegUpd.cf_arithFlags, reduceCtorEq, ite_false, Option.some.injEq, exists_eq_left']
    refine ⟨?_, fun r hr => ?_, rfl, rfl, rfl⟩
    · simp only [wordsVal, Nat.mul_zero, Nat.add_zero]
      rfl
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rw [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, ite_eq_right hr, RegUpd.gpr_setReg, ite_eq_right hr]
  | k + 1, ha, hm => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, WP.block_append_iff]
    refine WP.mono (ltSteps_ok hs k (by omega) (by omega)) fun s₁ ⟨c₁, k₁⟩ => ?_
    have hs₁ := hs.of_keeps k₁ (by decide)
    apply WP.of_runBlock
    simp only [ltStep_succ, runBlock_cons, runStep_some, runBlock_nil, exec,
      execAlu, readSrc, ld_sc hs₁ (d := a + 8 * (k + 1)) (by omega), Option.map_some, Option.bind_some,
      RegUpd.gpr_setReg, ite_true, RegUpd.mem_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg,
      State.load64, ea_sc, hs₁.rdi, ld_sc hs₁ (d := m + 8 * (k + 1)) (by omega), RegUpd.cf_setReg, c₁,
      RegUpd.cf_arithFlags, reduceCtorEq, ite_false, Option.some.injEq, exists_eq_left', k₁.2.1]
    refine ⟨?_, fun r hr => ?_, ?_, ?_, ?_⟩
    · refine decide_eq_decide.mpr ?_
      rw [wordsVal_succ_top s.mem base a (k + 1), wordsVal_succ_top s.mem base m (k + 1)]
      exact (lt_top (wordsVal_lt _ _ _ _) (wordsVal_lt _ _ _ _)).symm
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rw [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, ite_eq_right hr, RegUpd.gpr_setReg, ite_eq_right hr,
        k₁.1 r (by simpa using hr)]
    · rw [RegUpd.mem_setReg, RegUpd.mem_arithFlags, RegUpd.mem_setReg, k₁.2.1]
    · rw [RegUpd.rd_setReg, RegUpd.rd_arithFlags, RegUpd.rd_setReg, k₁.2.2.1]
    · rw [RegUpd.wr_setReg, RegUpd.wr_arithFlags, RegUpd.wr_setReg, k₁.2.2.2]

/-- `rax` is all ones iff `[a] < [MN]`; `rdx` changes too. -/
theorem ltN_ok (c : Cfg) {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {a : Nat}
    (hn : 0 < c.n) (ha : a + 8 * c.n ≤ size) (hm : c.sl MN + 8 * c.n ≤ size) :
    WP isa (.block (c.ltN a)) s fun s' =>
      s'.gpr .rax = mask (wordsVal s.mem base a c.n < wordsVal s.mem base (c.sl MN) c.n) ∧
      Keeps [.rax, .rdx] s s' := by
  obtain ⟨k, hk⟩ : ∃ k, c.n = k + 1 := ⟨c.n - 1, by omega⟩
  rw [ltN_eq, WP.block_append_iff, hk]
  rw [hk] at ha hm
  refine WP.mono (ltSteps_ok hs k ha hm) fun s₁ ⟨c₁, k₁⟩ => ?_
  refine WP.mono (sbbMask_ok s₁ c₁) fun s₂ ⟨e₂, k₂⟩ => ⟨?_, (k₁.mono (by sub_regs)).trans (k₂.mono (by sub_regs))⟩
  rw [e₂]
  simp only [mask, decide_eq_true_eq]

/-! ## The flag -/

/-- `[FLAG] &= rdx`. -/
theorem andFlag_ok (c : Cfg) {s : State} {base : Addr} {size : Nat} (hs : Scr s base size)
    (hf : c.sl FLAG + 8 ≤ size) :
    WP isa (.block c.andFlag) s fun s' =>
      s'.mem = s.mem.writeW (off base (c.sl FLAG)) (word s.mem base (c.sl FLAG) &&& s.gpr .rdx) ∧
      KeepRegs [.rax] s s' := by
  apply WP.of_runBlock
  simp only [Cfg.andFlag, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu, Option.map_some,
    Option.bind_some, State.load64, State.store64, ea_sc, RegUpd.gpr_setReg, RegUpd.gpr_arithFlags,
    RegUpd.rd_setReg, RegUpd.wr_setReg, RegUpd.mem_setReg, RegUpd.rd_arithFlags, RegUpd.wr_arithFlags,
    RegUpd.mem_arithFlags, reduceCtorEq, ite_true, ite_false, hs.rdi, ld_sc hs (d := c.sl FLAG) hf,
    st_sc hs (d := c.sl FLAG) hf, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, ⟨fun r hr => ?_, rfl, rfl⟩⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr, ite_false]

/-- The flag word after `andFlag`, and what else it keeps. -/
theorem andFlag_ok' (c : Cfg) {s : State} {base : Addr} {size : Nat} (hs : Scr s base size)
    (hf : c.sl FLAG + 8 ≤ size) :
    WP isa (.block c.andFlag) s fun s' =>
      word s'.mem base (c.sl FLAG) = word s.mem base (c.sl FLAG) &&& s.gpr .rdx ∧
      KeepRegs [.rax] s s' ∧ Outside base (c.sl FLAG) 8 s.mem s'.mem :=
  WP.mono (andFlag_ok c hs hf) fun s' ⟨m, k⟩ =>
    ⟨by rw [m, word_writeW_self], k, by rw [m]; exact writeW_outside _ _ _ (by have := hs.nowrap; omega)⟩

/-- `checkRange a`: the flag `&=` the mask of `0 < [a] < [MN]`. -/
theorem checkRange_ok (c : Cfg) {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {a : Nat}
    (hn : 0 < c.n) (ha : a + 8 * c.n ≤ size) (hm : c.sl MN + 8 * c.n ≤ size) (hf : c.sl FLAG + 8 ≤ size) :
    WP isa (.block (c.checkRange a)) s fun s' =>
      word s'.mem base (c.sl FLAG) = word s.mem base (c.sl FLAG) &&&
        mask (0 < wordsVal s.mem base a c.n ∧ wordsVal s.mem base a c.n < wordsVal s.mem base (c.sl MN) c.n) ∧
      KeepRegs [.rax, .rbp, .rcx, .rdx] s s' ∧ Outside base (c.sl FLAG) 8 s.mem s'.mem := by
  rw [Cfg.checkRange, List.append_assoc, List.append_assoc, List.append_assoc, WP.block_append_iff]
  refine WP.mono (ltN_ok c hs hn ha hm) fun s₁ ⟨e₁, k₁⟩ => ?_
  have hs₁ := hs.of_keeps k₁ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (show WP isa (.block [.mov .rbp (.reg .rax)]) s₁ (fun s₂ =>
      s₂.gpr .rbp = s₁.gpr .rax ∧ Keeps [.rbp] s₁ s₂) by
    apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, Option.map_some,
      RegUpd.gpr_setReg, ite_true, Option.some.injEq, exists_eq_left']
    refine ⟨trivial, fun r hr => ?_, rfl, rfl, rfl⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    simp only [RegUpd.gpr_setReg, hr, ite_false]) fun s₂ ⟨e₂, k₂⟩ => ?_
  have hs₂ := hs₁.of_keeps k₂ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (nonzero_ok c hs₂ hn ha) fun s₃ ⟨e₃, k₃⟩ => ?_
  have hs₃ := hs₂.of_keeps k₃ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (show WP isa (.block [.alu .and .rdx (.reg .rbp)]) s₃ (fun s₄ =>
      s₄.gpr .rdx = s₃.gpr .rdx &&& s₃.gpr .rbp ∧ Keeps [.rdx] s₃ s₄) by
    apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu, Option.bind_some,
      RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, ite_true, Option.some.injEq, exists_eq_left']
    refine ⟨trivial, fun r hr => ?_, rfl, rfl, rfl⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr, ite_false]) fun s₄ ⟨e₄, k₄⟩ => ?_
  have hs₄ := hs₃.of_keeps k₄ (by decide)
  refine WP.mono (andFlag_ok' c hs₄ hf) fun s₅ ⟨e₅, k₅, O₅⟩ => ?_
  have hm₄ : s₄.mem = s.mem := by rw [k₄.2.1, k₃.2.1, k₂.2.1, k₁.2.1]
  have hrbp : s₃.gpr .rbp = s₁.gpr .rax := by rw [k₃.1 _ (by decide), e₂]
  rw [k₂.2.1, k₁.2.1] at e₃
  refine ⟨?_, ?_, by rw [← hm₄]; exact O₅⟩
  · rw [e₅, hm₄, e₄, e₃, hrbp, e₁, mask_and]
    simp only [Nat.pos_iff_ne_zero]
  · exact ((((Keeps.regs k₁).mono (by sub_regs)).trans ((Keeps.regs k₂).mono (by sub_regs))).trans
      ((Keeps.regs k₃).mono (by sub_regs))).trans (((Keeps.regs k₄).mono (by sub_regs)).trans (k₅.mono (by sub_regs)))

/-- `checkNonzero a`: the flag `&=` the mask of `[a] ≠ 0`. -/
theorem checkNonzero_ok (c : Cfg) {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {a : Nat}
    (hn : 0 < c.n) (ha : a + 8 * c.n ≤ size) (hf : c.sl FLAG + 8 ≤ size) :
    WP isa (.block (c.checkNonzero a)) s fun s' =>
      word s'.mem base (c.sl FLAG) = word s.mem base (c.sl FLAG) &&& mask (wordsVal s.mem base a c.n ≠ 0) ∧
      KeepRegs [.rax, .rcx, .rdx] s s' ∧ Outside base (c.sl FLAG) 8 s.mem s'.mem := by
  rw [Cfg.checkNonzero, WP.block_append_iff]
  refine WP.mono (nonzero_ok c hs hn ha) fun s₁ ⟨e₁, k₁⟩ => ?_
  refine WP.mono (andFlag_ok' c (hs.of_keeps k₁ (by decide)) hf) fun s₂ ⟨e₂, k₂, O₂⟩ => ?_
  refine ⟨by rw [e₂, e₁, k₁.2.1], ((Keeps.regs k₁).mono (by sub_regs)).trans (k₂.mono (by sub_regs)),
    by rw [← k₁.2.1]; exact O₂⟩

end VG.Proof.Weierstrass.X86_64
