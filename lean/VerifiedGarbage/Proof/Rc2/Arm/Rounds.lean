import VerifiedGarbage.Impl.Rc2.Arm.Block
import VerifiedGarbage.Proof.Rc2.Arm.Lookup
import VerifiedGarbage.Proof.Rc2.Word32

/-! # RC2 mixing and mashing in Arm registers -/

namespace VG.Proof.Rc2.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.Rc2.Arm VG.Proof.Rc2.Word32

/-- State words never alias the temporaries or argument registers. -/
theorem wordReg_separate (i : Nat) :
    wordReg i ≠ .r12 ∧ wordReg i ≠ .r3 ∧ wordReg i ≠ .r2 ∧ wordReg i ≠ .r0 ∧
    wordReg i ≠ .r1 ∧ wordReg i ≠ .r8 ∧ wordReg i ≠ .r9 ∧
    wordReg i ≠ .r10 ∧ wordReg i ≠ .r11 := by
  have h : ∀ j < 4,
      wordReg j ≠ .r12 ∧ wordReg j ≠ .r3 ∧ wordReg j ≠ .r2 ∧ wordReg j ≠ .r0 ∧
      wordReg j ≠ .r1 ∧ wordReg j ≠ .r8 ∧ wordReg j ≠ .r9 ∧
      wordReg j ≠ .r10 ∧ wordReg j ≠ .r11 := by decide
  simpa only [wordReg, Nat.mod_mod] using h (i % 4) (Nat.mod_lt _ (by decide))

theorem wordReg_injective : ∀ i < 4, ∀ j < 4, wordReg i = wordReg j ↔ i = j := by decide

theorem rotation_bounds (i : Nat) : 1 ≤ Spec.Rc2.rotation i ∧ Spec.Rc2.rotation i < 16 := by
  have h : ∀ j < 4, 1 ≤ Spec.Rc2.rotation j ∧ Spec.Rc2.rotation j < 16 := by decide
  simpa only [Spec.Rc2.rotation, Nat.mod_mod] using h (i % 4) (Nat.mod_lt _ (by decide))

theorem rotate16_ok (s : State) (r : Reg) (hr : r ≠ .r12)
    (x : BitVec 16) (hx : s.gpr r = x.setWidth 32)
    (n : Nat) (hn : 1 ≤ n) (hn' : n < 16) :
    ∃ s', runBlock isa (rotate16 r n) s = some s' ∧
      s'.gpr r = (x.rotateLeft n).setWidth 32 ∧ Keep [r, .r12] s s' := by
  have hleft : 1 ≤ 32 - n ∧ 32 - n ≤ 31 := by omega
  have hright : 1 ≤ 16 - n ∧ 16 - n ≤ 31 := by omega
  refine ⟨_, by
    simp only [rotate16, mask, rr, List.cons_append, List.nil_append, runBlock_cons, runStep_some, runBlock_nil, exec, Op2.eval, Option.map_some, and_self, Nat.reduceSub, hleft, hright, show 1 ≤ 16 ∧ 16 ≤ 31 by decide, ite_true, hr, Ne.symm hr,
       gpr_setReg,
      ite_false]
    rfl, ?_⟩
  constructor
  · simp only [gpr_setReg, ite_true,
      hr, ite_false]
    rw [hx]
    rw [maskBits _ 16 (by decide), ← maskWord]
    exact rotateWord x n hn hn'
  · constructor
    · intro r' hr'
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr'
      simp only [gpr_setReg, hr'.1, hr'.2, ite_false]
    · simp only [mem_setReg]
    · simp only [rd_setReg]
    · simp only [wr_setReg]

theorem mixInputs_ok (s : State) (i j : Nat) (hj : j < 64)
    (fit : (s.gpr .r0).toNat + 128 ≤ 2 ^ 32)
    (readable : ∀ k < 128,
      InRegions (s.rd ++ s.wr) (State.addr (s.gpr .r0 + BitVec.ofNat 32 k)) 1) :
    ∃ s', runBlock isa (mixInputs j i) s = some s' ∧
      s'.gpr .r10 = (s.gpr (wordReg (i + 3)) &&& s.gpr (wordReg (i + 2))) +
        (~~~(s.gpr (wordReg (i + 3))) &&& s.gpr (wordReg (i + 1))) ∧
      s'.gpr .r8 = ((Spec.Rc2.scheduleAt s.mem (State.addr (s.gpr .r0))).getD j 0).setWidth 32 ∧
      Keep [.r8, .r9, .r10, .r11] s s' := by
  have h₁ := wordReg_separate (i + 1)
  have h₂ := wordReg_separate (i + 2)
  have h₃ := wordReg_separate (i + 3)
  have lo := readable (2 * j) (by omega)
  have hi := readable (2 * j + 1) (by omega)
  have loOff : 2 * j < 4096 := by omega
  have hiOff : 2 * j + 1 < 4096 := by omega
  refine ⟨_, by
    simp (config := {decide := true}) only [mixInputs, loadKey, imm,
      List.cons_append, List.nil_append, runBlock_cons, runStep_some, runBlock_nil,
      exec, Op2.eval, State.load8,
      Option.map_some,
       gpr_setReg,
      mem_setReg, rd_setReg,
      wr_setReg, loOff, hiOff, lo, hi, ite_true, ite_false,
      h₁.2.2.2.2.2.2.2.1, h₁.2.2.2.2.2.2.2.2,
      h₃.2.2.2.2.2.2.2.1, h₃.2.2.2.2.2.2.2.2]
    rfl, ?_⟩
  refine ⟨?_, ?_, ?_⟩
  · simp only [gpr_setReg, reduceCtorEq, ite_true,
      ite_false]
    simp only [BitVec.setWidth_zero]
    have comp (x : BitVec 32) : 0#32 - x - 1 = ~~~x := by bv_omega
    rw [comp]
  · simp only [gpr_setReg, reduceCtorEq, ite_true, ite_false]
    rw [joinBytes, scheduleAt_getD _ _ _ hj]
    rw [addr_add (by omega_using [fit, hj]), addr_add (by omega_using [fit, hj])]
  · constructor
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp only [gpr_setReg,
        hr.1, hr.2.1, hr.2.2.1, hr.2.2.2, ite_false]
    · simp only [mem_setReg]
    · simp only [rd_setReg]
    · simp only [wr_setReg]

/-- Current RC2 words in the four dedicated registers. -/
def Words (s : State) (v : Spec.Rc2.State) : Prop :=
  ∀ i < 4, s.gpr (wordReg i) = (v.getD i 0).setWidth 32

def temps : List Reg := [.r12, .r3, .r8, .r9, .r10, .r11]
def roundWrites : List Reg := temps ++ [.r4, .r5, .r6, .r7]

theorem wordReg_not_temps (i : Nat) : wordReg i ∉ temps := by
  have h := wordReg_separate i
  simp only [temps, List.mem_cons, List.not_mem_nil, or_false, not_or]
  exact ⟨h.1, h.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2.1,
    h.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2⟩

theorem wordReg_mem_roundWrites (i : Nat) : wordReg i ∈ roundWrites := by
  have h : ∀ j < 4, wordReg j ∈ roundWrites := by decide
  simpa only [wordReg, Nat.mod_mod] using h (i % 4) (Nat.mod_lt _ (by decide))

theorem vector_getD {α : Type} {n : Nat} (v : Vector α n) (i : Nat) (hi : i < n) (d : α) :
    v.getD i d = v[i] := by
  simp [Vector.getD, hi]

theorem Words.update {s s' : State} {v : Spec.Rc2.State} (h : Words s v)
    (i : Nat) (hi : i < 4) (x : BitVec 16)
    (out : s'.gpr (wordReg i) = x.setWidth 32)
    (keep : Keep (wordReg i :: temps) s s') : Words s' (v.set! i x) := by
  intro j hj
  by_cases he : j = i
  · subst j
    simpa [Vector.getD, hi] using out
  · have hr : wordReg j ∉ wordReg i :: temps := by
      simp only [List.mem_cons, not_or]
      exact ⟨fun e => he ((wordReg_injective j hj i hi).mp e), wordReg_not_temps j⟩
    rw [keep.reg _ hr, h j hj]
    rw [vector_getD _ j hj, vector_getD _ j hj, Vector.getElem_set!_ne hj (Ne.symm he)]

theorem Words.preserve {s s' : State} {v : Spec.Rc2.State} (h : Words s v)
    (keep : Keep temps s s') : Words s' v := by
  intro i hi
  exact (keep.reg _ (wordReg_not_temps i)).trans (h i hi)

theorem Keep.round {s s' : State} {i : Nat}
    (h : Keep (wordReg i :: temps) s s') : Keep roundWrites s s' :=
  h.weaken (by
    intro r hr
    simp only [List.mem_cons] at hr
    rcases hr with he | hm
    · subst r; exact wordReg_mem_roundWrites i
    · exact List.mem_append_left _ hm)


theorem addInputs_ok (s : State) (r : Reg) (h6 : r ≠ .r10) :
    ∃ s', runBlock isa (addInputs r) s = some s' ∧
      s'.gpr r = (s.gpr r + s.gpr .r8 + s.gpr .r10) &&& 65535 ∧ Keep [r] s s' := by
  refine ⟨_, by
    simp (config := {decide := true}) only [addInputs, mask, List.cons_append, List.nil_append,
      runBlock_cons, runStep_some, runBlock_nil, exec, Op2.eval, Option.map_some,
      gpr_setReg, Ne.symm h6, ite_true, ite_false]
    rfl, ?_⟩
  constructor
  · simp only [gpr_setReg_self]
    rw [maskBits _ 16 (by decide), maskWord]
  · constructor
    · intro r' hr
      simp only [List.mem_singleton] at hr
      simp only [gpr_setReg, hr, ite_false]
    · rfl
    · rfl
    · rfl

theorem subInputs_ok (s : State) (r : Reg) (h6 : r ≠ .r10) :
    ∃ s', runBlock isa (subInputs r) s = some s' ∧
      s'.gpr r = (s.gpr r - s.gpr .r8 - s.gpr .r10) &&& 65535 ∧ Keep [r] s s' := by
  refine ⟨_, by
    simp (config := {decide := true}) only [subInputs, mask, List.cons_append, List.nil_append,
      runBlock_cons, runStep_some, runBlock_nil, exec, Op2.eval, Option.map_some,
      gpr_setReg, Ne.symm h6, ite_true, ite_false]
    rfl, ?_⟩
  constructor
  · simp only [gpr_setReg_self]
    rw [maskBits _ 16 (by decide), maskWord]
  · constructor
    · intro r' hr
      simp only [List.mem_singleton] at hr
      simp only [gpr_setReg, hr, ite_false]
    · rfl
    · rfl
    · rfl

theorem mix_ok (s : State) (v : Spec.Rc2.State) (hv : Words s v)
    (i j : Nat) (hi : i < 4) (hj : j < 64)
    (fit : (s.gpr .r0).toNat + 128 ≤ 2 ^ 32)
    (readable : ∀ k < 128,
      InRegions (s.rd ++ s.wr) (State.addr (s.gpr .r0 + BitVec.ofNat 32 k)) 1) :
    WP isa (.block (mix j i)) s (fun s' =>
      Words s' (Spec.Rc2.mix (Spec.Rc2.scheduleAt s.mem (State.addr (s.gpr .r0))) j i v) ∧
      Keep (wordReg i :: temps) s s') := by
  rw [mix, List.append_assoc, WP.block_append_iff]
  obtain ⟨s₁, run₁, composite₁, key₁, keep₁⟩ := mixInputs_ok s i j hj fit readable
  refine WP.of_runBlock ⟨s₁, run₁, ?_⟩
  rw [WP.block_append_iff]
  have sep := wordReg_separate i
  obtain ⟨s₂, run₂, out₂, keep₂⟩ := addInputs_ok s₁ (wordReg i)
    sep.2.2.2.2.2.2.2.1
  refine WP.of_runBlock ⟨s₂, run₂, ?_⟩
  let x := v.getD i 0 + (Spec.Rc2.scheduleAt s.mem (State.addr (s.gpr .r0))).getD j 0 +
    (v.getD ((i + 3) % 4) 0 &&& v.getD ((i + 2) % 4) 0) +
    (~~~(v.getD ((i + 3) % 4) 0) &&& v.getD ((i + 1) % 4) 0)
  have wordmod (j : Nat) : wordReg j = wordReg (j % 4) := by simp [wordReg]
  have value₂ : s₂.gpr (wordReg i) = x.setWidth 32 := by
    rw [out₂, key₁, composite₁, keep₁.reg (wordReg i) (by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
      exact ⟨sep.2.2.2.2.2.1, sep.2.2.2.2.2.2.1,
        sep.2.2.2.2.2.2.2.1, sep.2.2.2.2.2.2.2.2⟩), hv i hi,
      wordmod (i + 3), wordmod (i + 2), wordmod (i + 1),
      hv _ (Nat.mod_lt _ (by decide)), hv _ (Nat.mod_lt _ (by decide)),
      hv _ (Nat.mod_lt _ (by decide))]
    exact mixWord _ _ _ _ _
  have hn := rotation_bounds i
  obtain ⟨s₃, run₃, out₃, keep₃⟩ := rotate16_ok s₂ (wordReg i) sep.1 x value₂ _ hn.1 hn.2
  refine WP.of_runBlock ⟨s₃, run₃, ?_⟩
  have k₁ : Keep (wordReg i :: temps) s s₁ := keep₁.weaken (by
    intro r hr
    apply List.mem_cons_of_mem
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with h | h | h | h <;> subst r <;> decide)
  have k₂ : Keep (wordReg i :: temps) s₁ s₂ := keep₂.weaken (by
    intro r hr
    simp only [List.mem_singleton] at hr
    subst r; exact List.mem_cons_self)
  have k₃ : Keep (wordReg i :: temps) s₂ s₃ := keep₃.weaken (by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with h | h
    · subst r; exact List.mem_cons_self
    · subst r; exact List.mem_cons_of_mem _ (by decide))
  have keep := (k₁.trans k₂).trans k₃
  exact ⟨hv.update i hi (x.rotateLeft _) out₃ keep, keep⟩

theorem wordReg_mod (i : Nat) : wordReg i = wordReg (i % 4) := by simp [wordReg]

theorem wordReg_offset_ne (i : Nat) (hi : i < 4) (d : Nat) (hd : 1 ≤ d) (hd' : d < 4) :
    wordReg (i + d) ≠ wordReg i := by
  rw [wordReg_mod (i + d)]
  intro he
  have := (wordReg_injective _ (Nat.mod_lt _ (by decide)) i hi).mp he
  omega

theorem keep_inputs {s s' : State} (h : Keep [.r8, .r9, .r10, .r11] s s') (i : Nat) :
    Keep (wordReg i :: temps) s s' := h.weaken (by
  intro r hr
  apply List.mem_cons_of_mem
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with h | h | h | h <;> subst r <;> decide)

theorem keep_rotate {i : Nat} {s s' : State} (h : Keep [wordReg i, .r12] s s') :
    Keep (wordReg i :: temps) s s' := h.weaken (by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with h | h
  · subst r; exact List.mem_cons_self
  · subst r; exact List.mem_cons_of_mem _ (by decide))

theorem keep_word {i : Nat} {s s' : State} (h : Keep [wordReg i] s s') :
    Keep (wordReg i :: temps) s s' := h.weaken (by
  intro r hr
  simp only [List.mem_singleton] at hr
  subst r; exact List.mem_cons_self)

theorem reverseMix_ok (s : State) (v : Spec.Rc2.State) (hv : Words s v)
    (i j : Nat) (hi : i < 4) (hj : j < 64)
    (fit : (s.gpr .r0).toNat + 128 ≤ 2 ^ 32)
    (readable : ∀ k < 128,
      InRegions (s.rd ++ s.wr) (State.addr (s.gpr .r0 + BitVec.ofNat 32 k)) 1) :
    WP isa (.block (reverseMix j i)) s (fun s' =>
      Words s' (Spec.Rc2.reverseMix (Spec.Rc2.scheduleAt s.mem (State.addr (s.gpr .r0))) j i v) ∧
      Keep (wordReg i :: temps) s s') := by
  rw [reverseMix, List.append_assoc, WP.block_append_iff]
  have sep := wordReg_separate i
  have hn := rotation_bounds i
  obtain ⟨s₁, run₁, out₁, keep₁⟩ := rotate16_ok s (wordReg i) sep.1 (v.getD i 0)
    (hv i hi) (16 - Spec.Rc2.rotation i) (by omega) (by omega)
  rw [rotateLeft_reverse _ _ hn.1 hn.2] at out₁
  refine WP.of_runBlock ⟨s₁, run₁, ?_⟩
  rw [WP.block_append_iff]
  have ptr₁ : s₁.gpr .r0 = s.gpr .r0 := keep₁.reg _ (by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
    exact ⟨Ne.symm sep.2.2.2.1, by decide⟩)
  have read₁ : ∀ k < 128,
      InRegions (s₁.rd ++ s₁.wr) (State.addr (s₁.gpr .r0 + BitVec.ofNat 32 k)) 1 := by
    rw [keep₁.rd, keep₁.wr, ptr₁]; exact readable
  obtain ⟨s₂, run₂, composite₂, key₂, keep₂⟩ := mixInputs_ok s₁ i j hj (by rw [ptr₁]; exact fit) read₁
  refine WP.of_runBlock ⟨s₂, run₂, ?_⟩
  obtain ⟨s₃, run₃, out₃, keep₃⟩ := subInputs_ok s₂ (wordReg i) sep.2.2.2.2.2.2.2.1
  refine WP.of_runBlock ⟨s₃, run₃, ?_⟩
  have other (d : Nat) (hd : 1 ≤ d) (hd' : d < 4) :
      s₁.gpr (wordReg (i + d)) = (v.getD ((i + d) % 4) 0).setWidth 32 := by
    rw [keep₁.reg _ (by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
      exact ⟨wordReg_offset_ne i hi d hd hd', (wordReg_separate _).1⟩),
      wordReg_mod (i + d)]
    exact hv _ (Nat.mod_lt _ (by decide))
  have keptWord := keep₂.reg (wordReg i) (by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
    exact ⟨sep.2.2.2.2.2.1, sep.2.2.2.2.2.2.1,
      sep.2.2.2.2.2.2.2.1, sep.2.2.2.2.2.2.2.2⟩)
  have value₃ : s₃.gpr (wordReg i) =
      ((v.getD i 0).rotateRight (Spec.Rc2.rotation i) -
        (Spec.Rc2.scheduleAt s.mem (State.addr (s.gpr .r0))).getD j 0 -
        (v.getD ((i + 3) % 4) 0 &&& v.getD ((i + 2) % 4) 0) -
        (~~~(v.getD ((i + 3) % 4) 0) &&& v.getD ((i + 1) % 4) 0)).setWidth 32 := by
    rw [out₃, keptWord, out₁, key₂, composite₂, keep₁.mem, ptr₁,
      other 3 (by decide) (by decide), other 2 (by decide) (by decide),
      other 1 (by decide) (by decide)]
    exact reverseMixWord _ _ _ _ _
  have keep := ((keep_rotate keep₁).trans (keep_inputs keep₂ i)).trans (keep_word keep₃)
  exact ⟨hv.update i hi _ value₃ keep, keep⟩

theorem adjust_ok (s : State) (r : Reg) (sub : Bool) :
    ∃ s', runBlock isa (adjust sub r) s = some s' ∧
      s'.gpr r = (if sub then s.gpr r - s.gpr .r12 else s.gpr r + s.gpr .r12) &&& 65535 ∧
      Keep [r] s s' := by
  cases sub <;> refine ⟨_, by
    simp (config := {decide := true}) only [adjust, mask, List.cons_append, List.nil_append,
      ite_false, ite_true, runBlock_cons, runStep_some,
      runBlock_nil, exec, Op2.eval, Option.map_some, gpr_setReg]
    rfl, ?_⟩
  all_goals
    constructor
    · simp only [gpr_setReg_self, Bool.false_eq_true,
        ite_false, ite_true]
      rw [maskBits _ 16 (by decide), maskWord]
    · constructor
      · intro r' hr
        simp only [List.mem_singleton] at hr
        simp only [gpr_setReg, hr, ite_false]
      · rfl
      · rfl
      · rfl

theorem indexWord (x : BitVec 16) :
    ((x.setWidth 32).setWidth 6).toNat = (x &&& 63).toNat := by
  simp only [BitVec.toNat_setWidth, BitVec.toNat_and]
  change x.toNat % 4294967296 % 64 = x.toNat &&& (2 ^ 6 - 1)
  rw [Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt (show x.toNat < 4294967296 by have := x.isLt; omega)]

def mashSpec (direction : Spec.Rc2.Direction) (k : Spec.Rc2.Schedule)
    (i : Nat) (v : Spec.Rc2.State) : Spec.Rc2.State :=
  match direction with
  | .encrypt => Spec.Rc2.mash k i v
  | .decrypt => Spec.Rc2.reverseMash k i v

theorem mash_ok (direction : Spec.Rc2.Direction) (s : State)
    (v : Spec.Rc2.State) (hv : Words s v) (i : Nat) (hi : i < 4)
    (fit : (s.gpr .r0).toNat + 128 ≤ 2 ^ 32)
    (readable : ∀ k < 128,
      InRegions (s.rd ++ s.wr) (State.addr (s.gpr .r0 + BitVec.ofNat 32 k)) 1) :
    WP isa (.block (mash direction i)) s (fun s' =>
      Words s' (mashSpec direction (Spec.Rc2.scheduleAt s.mem (State.addr (s.gpr .r0))) i v) ∧
      Keep (wordReg i :: temps) s s') := by
  rw [mash, List.append_assoc, WP.block_append_iff]
  let s₁ := s.setReg .r12 (s.gpr (wordReg (i + 3)))
  refine WP.of_runBlock ⟨s₁, ?_, ?_⟩
  · simp only [rr, runBlock_cons, runStep_some, runBlock_nil, exec, Op2.eval, Option.map_some]
    rfl
  rw [WP.block_append_iff]
  have keep₁ : Keep temps s s₁ := by
    constructor
    · intro r hr
      exact gpr_setReg_of_ne _ _ (fun he => hr (he ▸ List.mem_cons_self))
    · exact mem_setReg _ _ _
    · exact rd_setReg _ _ _
    · exact wr_setReg _ _ _
  have ptr₁ := keep₁.reg .r0 (by decide)
  have read₁ : ∀ k < 128,
      InRegions (s₁.rd ++ s₁.wr) (State.addr (s₁.gpr .r0 + BitVec.ofNat 32 k)) 1 := by
    rw [keep₁.rd, keep₁.wr, ptr₁]; exact readable
  apply WP.mono (keyLookup_ok s₁ (by rw [ptr₁]; exact fit) read₁)
  intro s₂ h₂
  let k := Spec.Rc2.scheduleAt s.mem (State.addr (s.gpr .r0))
  let key := k.getD ((v.getD ((i + 3) % 4) 0 &&& 63).toNat) 0
  have out₂ : s₂.gpr .r12 = key.setWidth 32 := by
    rw [h₂.1, keep₁.mem, ptr₁]
    change (k.getD (((s.gpr (wordReg (i + 3))).setWidth 6).toNat) 0).setWidth 32 = _
    rw [wordReg_mod (i + 3), hv _ (Nat.mod_lt _ (by decide)), indexWord]
  have keep₂ : Keep temps s₁ s₂ := h₂.2
  have value₂ := ((hv.preserve keep₁).preserve keep₂) i hi
  obtain ⟨s₃, run₃, out₃, keep₃⟩ := adjust_ok s₂ (wordReg i) (direction == .decrypt)
  refine WP.of_runBlock ⟨s₃, run₃, ?_⟩
  have keep : Keep (wordReg i :: temps) s s₃ :=
    ((keep₁.trans keep₂).weaken (fun _ hr => List.mem_cons_of_mem _ hr)).trans (keep_word keep₃)
  have out₃' : s₃.gpr (wordReg i) =
      (if direction == .decrypt then v.getD i 0 - key else v.getD i 0 + key).setWidth 32 := by
    rw [out₃, value₂, out₂]
    cases direction <;>
      simp [maskWord_lit, BitVec.sub_eq_add_neg, BitVec.setWidth_add, BitVec.setWidth_neg_of_le]
  constructor
  · cases direction <;> exact hv.update i hi _ out₃' keep
  · exact keep

end VG.Proof.Rc2.Arm
