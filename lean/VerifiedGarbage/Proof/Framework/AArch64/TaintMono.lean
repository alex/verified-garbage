import VerifiedGarbage.Proof.Framework.AArch64.VectorTaint
import VerifiedGarbage.Proof.Framework.TaintSum

/-!
# The AArch64 taint analyses are monotone

With more registers public on entry, every step of `AArch64.taint` and
`AArch64.VectorTaint.taint` succeeds, with more registers public after it
(`Taint.Mono`), so their checks can use summaries of called functions
(`taint_decide_sum`).
-/

namespace VG

namespace RegSet

variable {R : Type} [RegIdx R]

omit [RegIdx R] in
theorem subset_iff {a b : RegSet R} :
    a.subset b = true ↔ ∀ i, a.bits.testBit i = true → b.bits.testBit i = true := by
  rw [subset_eq, beq_iff_eq]
  constructor
  · intro h i hi
    rw [← h, Nat.testBit_and, Bool.and_eq_true] at hi
    exact hi.2
  · intro h
    apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.testBit_and]
    cases ha : a.bits.testBit i
    · rfl
    · rw [h i ha]; rfl

omit [RegIdx R] in
theorem subset_refl (a : RegSet R) : a.subset a = true := subset_iff.mpr fun _ h => h

omit [RegIdx R] in
theorem subset_trans {a b c : RegSet R} (h₁ : a.subset b = true) (h₂ : b.subset c = true) :
    a.subset c = true :=
  subset_iff.mpr fun i h => subset_iff.mp h₂ i (subset_iff.mp h₁ i h)

omit [RegIdx R] in
theorem empty_subset (a : RegSet R) : (empty : RegSet R).subset a = true :=
  subset_iff.mpr fun i h => by simp [empty] at h

theorem insert_mono {a b : RegSet R} (h : a.subset b = true) (r : R) :
    (a.insert r).subset (b.insert r) = true := by
  refine subset_iff.mpr fun i hi => ?_
  rw [insert_bits, Nat.testBit_or, Bool.or_eq_true] at hi ⊢
  exact hi.imp (subset_iff.mp h i) id

theorem erase_mono {a b : RegSet R} (h : a.subset b = true) (r : R) :
    (a.erase r).subset (b.erase r) = true := by
  refine subset_iff.mpr fun i hi => ?_
  rw [erase_bits, Nat.testBit_xor, Nat.testBit_and] at hi ⊢
  cases ha : a.bits.testBit i <;> cases hr : (bit r).testBit i <;> simp_all [subset_iff.mp h i]

theorem erase_subset (a : RegSet R) (r : R) : (a.erase r).subset a = true := by
  refine subset_iff.mpr fun i hi => ?_
  rw [erase_bits, Nat.testBit_xor, Nat.testBit_and] at hi
  cases ha : a.bits.testBit i <;> simp_all

theorem subset_insert (a : RegSet R) (r : R) : a.subset (a.insert r) = true := by
  refine subset_iff.mpr fun i hi => ?_
  rw [insert_bits, Nat.testBit_or, hi, Bool.true_or]

omit [RegIdx R] in
theorem inter_mono {a b c d : RegSet R} (h₁ : a.subset c = true) (h₂ : b.subset d = true) :
    (a.inter b).subset (c.inter d) = true := by
  refine subset_iff.mpr fun i hi => ?_
  rw [inter_bits, Nat.testBit_and, Bool.and_eq_true] at hi ⊢
  exact ⟨subset_iff.mp h₁ i hi.1, subset_iff.mp h₂ i hi.2⟩

theorem mem_mono {a b : RegSet R} (h : a.subset b = true) {r : R} (hr : a.mem r = true) :
    b.mem r = true := mem_of_subset h hr

/-- The union of two sets. -/
def union (a b : RegSet R) : RegSet R := ⟨Nat.lor a.bits b.bits⟩

omit [RegIdx R] in
theorem subset_union_left (a b : RegSet R) : a.subset (a.union b) = true :=
  subset_iff.mpr fun i h => by
    show (a.bits ||| b.bits).testBit i = true
    rw [Nat.testBit_or, h, Bool.true_or]

omit [RegIdx R] in
theorem subset_union_right (a b : RegSet R) : b.subset (a.union b) = true :=
  subset_iff.mpr fun i h => by
    show (a.bits ||| b.bits).testBit i = true
    rw [Nat.testBit_or, h, Bool.or_true]

omit [RegIdx R] in
theorem union_subset {a b c : RegSet R} (ha : a.subset c = true) (hb : b.subset c = true) :
    (a.union b).subset c = true :=
  subset_iff.mpr fun i h => by
    have h : (a.bits ||| b.bits).testBit i = true := h
    rw [Nat.testBit_or, Bool.or_eq_true] at h
    exact h.elim (subset_iff.mp ha i) (subset_iff.mp hb i)

omit [RegIdx R] in
theorem inter_subset_left (a b : RegSet R) : (a.inter b).subset a = true :=
  subset_iff.mpr fun i h => by
    rw [inter_bits, Nat.testBit_and, Bool.and_eq_true] at h; exact h.1

omit [RegIdx R] in
theorem inter_subset_right (a b : RegSet R) : (a.inter b).subset b = true :=
  subset_iff.mpr fun i h => by
    rw [inter_bits, Nat.testBit_and, Bool.and_eq_true] at h; exact h.2

omit [RegIdx R] in
theorem subset_inter {a b c : RegSet R} (hb : a.subset b = true) (hc : a.subset c = true) :
    a.subset (b.inter c) = true :=
  subset_iff.mpr fun i h => by
    rw [inter_bits, Nat.testBit_and, subset_iff.mp hb i h, subset_iff.mp hc i h]; rfl

omit [RegIdx R] in
theorem subset_of_bits_zero {a : RegSet R} (h : a.bits = 0) (b : RegSet R) :
    a.subset b = true :=
  subset_iff.mpr fun i hi => by rw [h, Nat.zero_testBit] at hi; cases hi

/-- `Φ` stays a subset of `σ` with `d` changed, if `d` is not in `F ⊇ Φ`. -/
theorem subset_insert_of {Φ σ : RegSet R} (hΦ : Φ.subset σ = true)
    (d : R) : Φ.subset (σ.insert d) = true :=
  subset_trans hΦ (subset_insert σ d)

theorem subset_erase_of {Φ F σ : RegSet R} (hΦF : Φ.subset F = true) (hΦ : Φ.subset σ = true)
    {d : R} (hd : F.mem d = false) : Φ.subset (σ.erase d) = true := by
  refine subset_iff.mpr fun i hi => ?_
  rw [erase_bits, Nat.testBit_xor, Nat.testBit_and, subset_iff.mp hΦ i hi, testBit_bit]
  have hF := subset_iff.mp hΦF i hi
  have hne : RegIdx.idx d ≠ i := by
    intro e
    have : F.mem d = true := (mem_iff (s := F) (r := d)).mpr (e ▸ hF)
    rw [hd] at this; cases this
  simp [hne]

end RegSet

namespace AArch64.Taint

theorem pub_mono {τ σ : T} (h : τ.subset σ = true) {r : Reg} (hr : pub τ r = true) :
    pub σ r = true := RegSet.mem_of_subset h hr

theorem set_mono {τ σ : T} (h : τ.subset σ = true) (d : Reg) {p q : Bool}
    (hpq : p = true → q = true) : (set τ d p).subset (set σ d q) = true := by
  unfold set
  cases p <;> cases q <;> simp only [Bool.false_eq_true, ite_true, ite_false]
  · exact RegSet.erase_mono h d
  · exact RegSet.subset_trans (RegSet.erase_subset τ d)
      (RegSet.subset_trans h (RegSet.subset_insert σ d))
  · exact absurd (hpq rfl) Bool.false_ne_true
  · exact RegSet.insert_mono h d

theorem step_mono {τ σ τ' : T} (i : Instr) (h : τ.subset σ = true) (hs : step τ i = some τ') :
    ∃ σ', step σ i = some σ' ∧ τ'.subset σ' = true := by
  have and2 : ∀ {a b : Reg}, (pub τ a && pub τ b) = true → (pub σ a && pub σ b) = true :=
    fun hab => by
      simp only [Bool.and_eq_true] at hab ⊢; exact ⟨pub_mono h hab.1, pub_mono h hab.2⟩
  cases i <;> simp only [step, reduceCtorEq] at hs ⊢
  all_goals first
    | (cases hs; exact ⟨_, rfl, set_mono h _ and2⟩)
    | (cases hs; exact ⟨_, rfl, set_mono h _ (pub_mono h)⟩)
    | (cases hs; exact ⟨_, rfl, set_mono h _ id⟩)
    | (cases hs; exact ⟨_, rfl, h⟩)
    | (cases hs; refine ⟨_, rfl, set_mono h _ fun hp => ?_⟩
       simp only [Bool.and_eq_true] at hp ⊢
       exact ⟨⟨pub_mono h hp.1.1, pub_mono h hp.1.2⟩, pub_mono h hp.2⟩)
    | (split at hs <;> [rename_i hn; cases hs]
       cases hs
       exact ⟨_, by simp only [pub_mono h hn, ↓reduceIte]; rfl, (by first | exact set_mono h _ id | exact h)⟩)

instance : VG.Taint.Mono AArch64.taint where
  le_refl := RegSet.subset_refl
  le_trans := RegSet.subset_trans
  step i h hs := step_mono i h hs
  condPub c h hc := by cases c <;> exact pub_mono h hc
  meet h₁ h₂ := RegSet.inter_mono h₁ h₂
  call h hs := by
    cases hs
    exact ⟨_, rfl, RegSet.erase_mono (RegSet.erase_mono (RegSet.erase_mono h _) _) _⟩
  ret h hs := by cases hs; exact ⟨_, rfl, h⟩
  push i h hs := by
    cases i <;> simp only [AArch64.taint, push, reduceCtorEq] at hs ⊢ <;> cases hs <;>
      exact ⟨_, rfl, h⟩
  pop i h hs := by
    cases i <;> simp only [AArch64.taint, pop, reduceCtorEq] at hs ⊢ <;> cases hs
    · exact ⟨_, rfl, RegSet.erase_mono h _⟩
    · exact ⟨_, rfl, h⟩

/-- The general-purpose register an instruction writes, if any. -/
def gprDst : Instr → Option Reg
  | .add _ d .. | .sub _ d .. | .adds _ d .. | .subs _ d .. | .logic _ _ d .. | .logicRor _ _ d ..
  | .bicRor _ d .. | .extr _ d .. | .mul _ d .. | .umulh d .. | .adcs _ d .. | .sbcs _ d ..
  | .adc _ d .. | .sbc _ d ..
  | .madd _ d .. | .addImm _ d .. | .subImm _ d .. | .ror _ d .. | .lsr _ d .. | .lsl _ d ..
  | .rev32 d _ | .rev d _ | .addSp d _ | .movz _ d .. | .movk _ d .. | .ldr _ d .. | .ldrb d ..
  | .ldrSp d _ | .umov _ d .. | .pop d => some d
  | _ => none

/-- `i` writes no register of `F`. -/
def keepsI (F : T) (i : Instr) : Bool :=
  match gprDst i with
  | some d => !F.mem d
  | none => true

theorem set_keeps {Φ F σ : T} (hΦF : Φ.subset F = true) (hΦ : Φ.subset σ = true) {d : Reg}
    (hd : F.mem d = false) (p : Bool) : Φ.subset (set σ d p) = true := by
  unfold set
  cases p
  · exact RegSet.subset_erase_of hΦF hΦ hd
  · exact RegSet.subset_insert_of hΦ d

theorem step_keeps {F Φ σ σ' : T} (i : Instr) (hk : keepsI F i = true) (hΦF : Φ.subset F = true)
    (hΦ : Φ.subset σ = true) (hs : step σ i = some σ') : Φ.subset σ' = true := by
  cases i <;> simp only [step, reduceCtorEq] at hs <;>
    simp only [keepsI, gprDst, Bool.not_eq_true'] at hk
  all_goals first
    | (cases hs; exact set_keeps hΦF hΦ hk _)
    | (cases hs; exact hΦ)
    | (split at hs <;> [skip; cases hs]
       cases hs
       first | exact set_keeps hΦF hΦ hk _ | exact hΦ)

end AArch64.Taint

namespace AArch64.VectorTaint

theorem setV_mono {τ σ : RegSet VReg} (h : τ.subset σ = true) (d : VReg) {p q : Bool}
    (hpq : p = true → q = true) : (setV τ d p).subset (setV σ d q) = true := by
  unfold setV
  cases p <;> cases q <;> simp only [Bool.false_eq_true, ite_true, ite_false]
  · exact RegSet.erase_mono h d
  · exact RegSet.subset_trans (RegSet.erase_subset τ d)
      (RegSet.subset_trans h (RegSet.subset_insert σ d))
  · exact absurd (hpq rfl) Bool.false_ne_true
  · exact RegSet.insert_mono h d

theorem afterV_mono {τ σ : RegSet VReg} (h : τ.subset σ = true) (i : Instr) :
    (afterV τ i).subset (afterV σ i) = true := by
  unfold afterV
  split
  · exact h
  · exact RegSet.subset_refl _

theorem le_iff {τ σ : T} : taint.le τ σ = true ↔ τ.1.subset σ.1 = true ∧ τ.2.subset σ.2 = true := by
  show (τ.1.subset σ.1 && τ.2.subset σ.2) = true ↔ _
  rw [Bool.and_eq_true]

theorem step_mono {τ σ τ' : T} (i : Instr) (h : taint.le τ σ = true) (hs : step τ i = some τ') :
    ∃ σ', step σ i = some σ' ∧ taint.le τ' σ' = true := by
  rw [le_iff] at h
  have ordinary : (Taint.step τ.1 i).map (fun g => (g, afterV τ.2 i)) = some τ' →
      ∃ σ', (Taint.step σ.1 i).map (fun g => (g, afterV σ.2 i)) = some σ' ∧
        taint.le τ' σ' = true := fun hs => by
    obtain ⟨g, hg, rfl⟩ := Option.map_eq_some_iff.mp hs
    obtain ⟨g', hg', hle⟩ := Taint.step_mono i h.1 hg
    exact ⟨_, by rw [hg']; rfl, le_iff.mpr ⟨hle, afterV_mono h.2 i⟩⟩
  cases i with
  | vop op =>
    cases op <;> try exact ordinary hs
    case dup a d n =>
      simp only [step, Option.some.injEq] at hs; subst hs
      exact ⟨_, rfl, le_iff.mpr ⟨h.1, setV_mono h.2 d (Taint.pub_mono h.1)⟩⟩
  | umov sz d n k =>
    simp only [step, Option.some.injEq] at hs; subst hs
    exact ⟨_, rfl, le_iff.mpr ⟨Taint.set_mono h.1 d (RegSet.mem_mono h.2), h.2⟩⟩
  | _ => exact ordinary hs

instance : VG.Taint.Mono taint where
  le_refl τ := le_iff.mpr ⟨RegSet.subset_refl _, RegSet.subset_refl _⟩
  le_trans {_ _ _} h₁ h₂ :=
    le_iff.mpr ⟨RegSet.subset_trans (le_iff.mp h₁).1 (le_iff.mp h₂).1,
      RegSet.subset_trans (le_iff.mp h₁).2 (le_iff.mp h₂).2⟩
  step i h hs := step_mono i h hs
  condPub c h hc := VG.Taint.Mono.condPub (A := AArch64.taint) c (le_iff.mp h).1 hc
  meet {_ _ _ _} h₁ h₂ :=
    le_iff.mpr ⟨RegSet.inter_mono (le_iff.mp h₁).1 (le_iff.mp h₂).1,
      RegSet.inter_mono (le_iff.mp h₁).2 (le_iff.mp h₂).2⟩
  call {τ σ τ'} h hs := by
    have hs : (AArch64.taint.call τ.1).map (fun g => (g, τ.2)) = some τ' := hs
    obtain ⟨g, hg, rfl⟩ := Option.map_eq_some_iff.mp hs
    obtain ⟨g', hg', hle⟩ := VG.Taint.Mono.call (A := AArch64.taint) (le_iff.mp h).1 hg
    refine ⟨(g', σ.2), ?_, le_iff.mpr ⟨hle, (le_iff.mp h).2⟩⟩
    show (AArch64.taint.call σ.1).map (fun g => (g, σ.2)) = _
    rw [hg']; rfl
  ret h hs := by cases hs; exact ⟨_, rfl, h⟩
  push {τ σ τ'} i h hs := by
    have hs : (Taint.push τ.1 i).map (fun g => (g, τ.2)) = some τ' := hs
    obtain ⟨g, hg, rfl⟩ := Option.map_eq_some_iff.mp hs
    obtain ⟨g', hg', hle⟩ := VG.Taint.Mono.push (A := AArch64.taint) i (le_iff.mp h).1 hg
    refine ⟨(g', σ.2), ?_, le_iff.mpr ⟨hle, (le_iff.mp h).2⟩⟩
    show (Taint.push σ.1 i).map (fun g => (g, σ.2)) = _
    rw [show Taint.push σ.1 i = some g' from hg']; rfl
  pop {τ σ τ'} i h hs := by
    have hs : (Taint.pop τ.1 i).map (fun g => (g, τ.2)) = some τ' := hs
    obtain ⟨g, hg, rfl⟩ := Option.map_eq_some_iff.mp hs
    obtain ⟨g', hg', hle⟩ := VG.Taint.Mono.pop (A := AArch64.taint) i (le_iff.mp h).1 hg
    refine ⟨(g', σ.2), ?_, le_iff.mpr ⟨hle, (le_iff.mp h).2⟩⟩
    show (Taint.pop σ.1 i).map (fun g => (g, σ.2)) = _
    rw [show Taint.pop σ.1 i = some g' from hg']; rfl

/-- An instruction keeps what is public of `F`, a set of general-purpose
registers it does not write (and no vector register). -/
def keeps (F : T) (i : Instr) : Bool := F.2.bits == 0 && Taint.keepsI F.1 i

theorem keeps_vec {F : T} {i : Instr} (h : keeps F i = true) : F.2.bits = 0 := by
  simp only [keeps, Bool.and_eq_true, beq_iff_eq] at h; exact h.1

theorem keeps_gpr {F : T} {i : Instr} (h : keeps F i = true) : Taint.keepsI F.1 i = true := by
  simp only [keeps, Bool.and_eq_true] at h; exact h.2

theorem vec_sub {Φ F : T} (hΦF : taint.le Φ F = true) (h0 : F.2.bits = 0) (s : RegSet VReg) :
    Φ.2.subset s = true := by
  have h := (le_iff.mp hΦF).2
  refine RegSet.subset_iff.mpr fun i hi => ?_
  have := RegSet.subset_iff.mp h i hi
  rw [h0, Nat.zero_testBit] at this; cases this

theorem step_keeps {F Φ σ σ' : T} (i : Instr) (hk : keeps F i = true) (hΦF : taint.le Φ F = true)
    (hΦ : taint.le Φ σ = true) (hs : step σ i = some σ') : taint.le Φ σ' = true := by
  have hv := vec_sub hΦF (keeps_vec hk)
  have hg := keeps_gpr hk
  have hΦF' := (le_iff.mp hΦF).1
  have hΦ' := (le_iff.mp hΦ).1
  have ordinary : (Taint.step σ.1 i).map (fun g => (g, afterV σ.2 i)) = some σ' →
      taint.le Φ σ' = true := fun hs => by
    obtain ⟨g, hg', rfl⟩ := Option.map_eq_some_iff.mp hs
    exact le_iff.mpr ⟨Taint.step_keeps i hg hΦF' hΦ' hg', hv _⟩
  cases i with
  | vop op =>
    cases op <;> try exact ordinary hs
    case dup a d n =>
      simp only [step, Option.some.injEq] at hs; subst hs
      exact le_iff.mpr ⟨hΦ', hv _⟩
  | umov sz d n k =>
    simp only [step, Option.some.injEq] at hs; subst hs
    simp only [Taint.keepsI, Taint.gprDst, Bool.not_eq_true'] at hg
    exact le_iff.mpr ⟨Taint.set_keeps hΦF' hΦ' hg _, hv _⟩
  | _ => exact ordinary hs

/-- A call writes `x16`, `x17` and `x30`. -/
def keepsCall (F : T) : Bool :=
  F.2.bits == 0 && !F.1.mem .x16 && !F.1.mem .x17 && !F.1.mem .x30

instance : VG.Taint.Frame taint where
  join a b := (a.1.union b.1, a.2.union b.2)
  bot := (RegSet.empty, RegSet.empty)
  le_join_left a b := le_iff.mpr ⟨RegSet.subset_union_left _ _, RegSet.subset_union_left _ _⟩
  le_join_right a b := le_iff.mpr ⟨RegSet.subset_union_right _ _, RegSet.subset_union_right _ _⟩
  join_le ha hb := le_iff.mpr ⟨RegSet.union_subset (le_iff.mp ha).1 (le_iff.mp hb).1,
    RegSet.union_subset (le_iff.mp ha).2 (le_iff.mp hb).2⟩
  meet_le_left a b := le_iff.mpr ⟨RegSet.inter_subset_left _ _, RegSet.inter_subset_left _ _⟩
  meet_le_right a b := le_iff.mpr ⟨RegSet.inter_subset_right _ _, RegSet.inter_subset_right _ _⟩
  le_meet hb hc := le_iff.mpr ⟨RegSet.subset_inter (le_iff.mp hb).1 (le_iff.mp hc).1,
    RegSet.subset_inter (le_iff.mp hb).2 (le_iff.mp hc).2⟩
  bot_le a := le_iff.mpr ⟨RegSet.empty_subset _, RegSet.empty_subset _⟩
  keeps := keeps
  keepsCall := keepsCall
  keeps_bot i := by
    have h : ∀ d : Reg, (RegSet.empty : RegSet Reg).mem d = false := fun d => by
      simp [RegSet.mem, RegSet.empty]
    simp only [keeps, Taint.keepsI]
    split
    · rw [h]; rfl
    · rfl
  keepsCall_bot := rfl
  step_keeps i hk hΦF hΦ hs := step_keeps i hk hΦF hΦ hs
  call_keeps {F Φ σ σ'} hk hΦF hΦ hs := by
    have hs : (AArch64.taint.call σ.1).map (fun g => (g, σ.2)) = some σ' := hs
    obtain ⟨g, hg, rfl⟩ := Option.map_eq_some_iff.mp hs
    cases hg
    simp only [keepsCall, Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at hk
    have hΦF' := (le_iff.mp hΦF).1
    have hΦ' := (le_iff.mp hΦ).1
    refine le_iff.mpr ⟨?_, (le_iff.mp hΦ).2⟩
    exact RegSet.subset_erase_of hΦF' (RegSet.subset_erase_of hΦF'
      (RegSet.subset_erase_of hΦF' hΦ' hk.1.1.2) hk.1.2) hk.2
  ret_keeps _ _ hΦ hs := by cases hs; exact hΦ
  push_keeps {F Φ σ σ'} i hk hΦF hΦ hs := by
    have hs : (Taint.push σ.1 i).map (fun g => (g, σ.2)) = some σ' := hs
    obtain ⟨g, hg, rfl⟩ := Option.map_eq_some_iff.mp hs
    cases i <;> simp only [Taint.push, reduceCtorEq, Option.some.injEq] at hg <;> subst hg <;>
      exact hΦ
  pop_keeps {F Φ σ σ'} i hk hΦF hΦ hs := by
    have hs : (Taint.pop σ.1 i).map (fun g => (g, σ.2)) = some σ' := hs
    obtain ⟨g, hg, rfl⟩ := Option.map_eq_some_iff.mp hs
    have hg' := keeps_gpr hk
    cases i <;> simp only [Taint.pop, reduceCtorEq, Option.some.injEq] at hg <;> subst hg
    · simp only [Taint.keepsI, Taint.gprDst, Bool.not_eq_true'] at hg'
      exact le_iff.mpr ⟨RegSet.subset_erase_of (le_iff.mp hΦF).1 (le_iff.mp hΦ).1 hg',
        (le_iff.mp hΦ).2⟩
    · exact hΦ

end AArch64.VectorTaint

end VG
