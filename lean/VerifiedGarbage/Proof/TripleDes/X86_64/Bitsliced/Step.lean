import VerifiedGarbage.Proof.TripleDes.X86_64.Bitsliced.Machine
import VerifiedGarbage.Proof.TripleDes.Bitslice.Pass

/-!
# One S-box of a bitsliced round, and the exchange of the halves

`sboxStep_ok`: the code of S-box `j` (its inputs, the next six key bits of
`r15` as masks XORed with the words of `E`; its circuit; XORing its outputs
into their words) does to the state words what `step` does, given the key
bits at the top of `r15`, and shifts them out. `swapHalves_ok`: the
exchange of the halves does what `swapW` does.
-/

namespace VG.Proof.TripleDes.X86_64.Bitsliced

open VG VG.X86_64 VG.X86_64.Straight VG.X86_64.RegUpd VG.Bitslice VG.Impl.TripleDes.X86_64.Bitslice
open VG.Impl.TripleDes.Bitslice
open VG.Proof.TripleDes.Bitslice (step sboxIn sboxOut outIdx partner swapW)

/-- The all-zero or all-one word. -/
def maskVal (b : Bool) : BitVec 64 := if b then BitVec.allOnes 64 else 0

theorem add_self_eq (x : BitVec 64) : x + x = x <<< 1 := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.pow_one]
  congr 1
  omega

theorem add_self_carry (a : BitVec 64) : decide (2 ^ 64 ≤ a.toNat + a.toNat) = a.msb := by
  rw [BitVec.msb_eq_decide]
  have := a.isLt
  simp only [Nat.add_one_sub_one]
  apply decide_eq_decide.mpr
  constructor <;> intro h <;> omega

theorem sbb_self (a : BitVec 64) (c : Bool) : a - a - (BitVec.ofBool c).setWidth 64 = maskVal c := by
  cases c <;> simp [maskVal]

theorem msb_shiftLeft (R : BitVec 64) {n : Nat} (hn : n < 64) : (R <<< n).msb = R.getLsbD (63 - n) := by
  rw [BitVec.msb_eq_getLsbD_last, BitVec.getLsbD_shiftLeft]
  have : ¬ 63 < n := by omega
  simp [this, show (63 : Nat) < 64 by decide]

theorem getLsbD_mask (b : Bool) {p : Nat} (hp : p < 64) : (maskVal b).getLsbD p = b := by
  cases b
  · simp [maskVal]
  · simp only [maskVal, ite_true, BitVec.getLsbD_allOnes, hp, decide_true]

/-! ## Inputs -/

theorem inReg_ne : ∀ i < 6, inReg i ≠ .r15 ∧ inReg i ≠ .rcx ∧ inReg i ≠ .rsp := by decide

theorem inReg_inj' : ∀ a < 6, ∀ b < 6, inReg a = inReg b → a = b := by decide

/-- One input: the next key bit as a mask, XORed with slot `w`. -/
theorem inputStep_run {s : State} (h : Room s) {q : Reg} (hq : q ≠ .r15) (hc : q ≠ .rcx)
    {w : Nat} (hw : w < 128) :
    ∃ s', runBlock isa [.alu .add .r15 (.reg .r15), .alu .sbb q (.reg q), .alu .xor q (.mem (at_ w))] s
        = some s' ∧
      s'.gpr .r15 = s.gpr .r15 <<< 1 ∧ s'.gpr q = maskVal (s.gpr .r15).msb ^^^ sl s w ∧
      (∀ r, r ≠ q → r ≠ .r15 → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  let a := s.gpr .r15
  let s₁ := (arithFlags s (a + a) (decide (2 ^ 64 ≤ a.toNat + a.toNat)) (addOverflow a a (a + a))).setReg
    .r15 (a + a)
  have e₁ : exec (.alu .add .r15 (.reg .r15)) s = some s₁ := by
    simp only [exec, execAlu, readSrc, Option.bind_some]; rfl
  have cf₁ : s₁.cf = some a.msb := by
    simp only [s₁, cf_setReg, cf_arithFlags, add_self_carry]
  let b := s₁.gpr q
  let r := b - b - (BitVec.ofBool a.msb).setWidth 64
  let s₂ := (arithFlags s₁ r (decide (b.toNat < b.toNat + a.msb.toNat)) (subOverflow b b r)).setReg q r
  have e₂ : exec (.alu .sbb q (.reg q)) s₁ = some s₂ := by
    simp only [exec, execAlu, readSrc, Option.bind_some, cf₁, Option.map_some]; rfl
  have c₂ : s₂.gpr .rcx = s.gpr .rcx := by
    simp [s₂, s₁, gpr_setReg, Ne.symm hc]
  have m₂ : s₂.mem = s.mem := by simp [s₂, s₁, mem_setReg, mem_arithFlags]
  have rd₂ : s₂.rd = s.rd := by simp [s₂, s₁, rd_setReg, rd_arithFlags]
  have wr₂ : s₂.wr = s.wr := by simp [s₂, s₁, wr_setReg, wr_arithFlags]
  have h₂ : Room s₂ := h.congr c₂ wr₂
  let v := sl s w
  let x := s₂.gpr q ^^^ v
  let s₃ := (arithFlags s₂ x false false).setReg q x
  have e₃ : exec (.alu .xor q (.mem (at_ w))) s₂ = some s₃ := by
    simp only [exec, execAlu, readSrc, State.load64, ea_at, slot_readable h₂ hw, ite_true,
      Option.bind_some]
    have : s₂.mem.readW (wordAddr (s₂.gpr .rcx) w) 64 = v := by simp only [m₂, c₂]; rfl
    rw [this]
  refine ⟨s₃, ?_, ?_, ?_, fun r' h1 h2 => ?_, ?_, ?_, ?_⟩
  · rw [runBlock_cons, e₁, runStep_some, runBlock_cons, e₂, runStep_some, runBlock_cons, e₃,
      runStep_some, runBlock_nil]
  · simp [s₃, s₂, s₁, gpr_setReg, Ne.symm hq, add_self_eq, a]
  · simp only [s₃, gpr_setReg_self, x]
    congr 1
    simp only [s₂, gpr_setReg_self, r]
    exact sbb_self _ _
  · simp [s₃, s₂, s₁, gpr_setReg, h1, h2]
  · simp [s₃, mem_setReg, mem_arithFlags, m₂]
  · simp [s₃, rd_setReg, rd_arithFlags, rd₂]
  · simp [s₃, wr_setReg, wr_arithFlags, wr₂]

def inputsN (ρ : Role) (j n : Nat) : List Instr :=
  (List.range n).flatMap fun m => inputStep ρ j (5 - m)

theorem inputCode_eq (ρ : Role) (j : Nat) : inputCode ρ j = inputsN ρ j 6 := rfl

theorem inputsN_succ (ρ : Role) (j n : Nat) :
    inputsN ρ j (n + 1) = inputsN ρ j n ++ inputStep ρ j (5 - n) := by
  simp only [inputsN, List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
    List.append_nil]

theorem readSlot_lt : ∀ ρ : Role, ∀ j < 8, ∀ i < 6, stSlot (readWord ρ (eBit (inBit j i))) < 72 := by
  intro ρ; cases ρ <;> decide +kernel

theorem inputsN_ok (ρ : Role) {j : Nat} (hj : j < 8) {n : Nat} (hn : n ≤ 6) {s : State} (h : Room s) :
    ∃ s', runBlock isa (inputsN ρ j n) s = some s' ∧ s'.gpr .r15 = s.gpr .r15 <<< n ∧
      (∀ m < n, s'.gpr (inReg (5 - m)) = maskVal ((s.gpr .r15).getLsbD (63 - m)) ^^^
        sl s (stSlot (readWord ρ (eBit (inBit j (5 - m)))))) ∧
      s'.gpr .rcx = s.gpr .rcx ∧ s'.gpr .rsp = s.gpr .rsp ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  induction n with
  | zero => exact ⟨s, runBlock_nil, by simp, fun m hm => by omega, rfl, rfl, rfl, rfl, rfl⟩
  | succ n ih =>
    obtain ⟨s₁, run₁, k₁, in₁, c₁, sp₁, m₁, rd₁, wr₁⟩ := ih (by omega)
    have h₁ : Room s₁ := h.congr c₁ wr₁
    obtain ⟨hq, hc, hsp⟩ := inReg_ne (5 - n) (by omega)
    obtain ⟨s₂, run₂, k₂, q₂, o₂, m₂, rd₂, wr₂⟩ :=
      inputStep_run h₁ hq hc (w := stSlot (readWord ρ (eBit (inBit j (5 - n)))))
        (by have := readSlot_lt ρ j hj (5 - n) (by omega); omega)
    refine ⟨s₂, ?_, ?_, fun m hm => ?_, ?_, ?_, m₂.trans m₁, rd₂.trans rd₁, wr₂.trans wr₁⟩
    · rw [inputsN_succ]; exact runBlock_cat_some run₁ run₂
    · rw [k₂, k₁, ← BitVec.shiftLeft_add]
    · by_cases he : m = n
      · subst he
        rw [q₂, k₁, msb_shiftLeft _ (by omega)]
        simp only [sl, m₁, c₁]
      · have hne : inReg (5 - m) ≠ inReg (5 - n) := by
          intro e; have := inReg_inj' _ (by omega) _ (by omega) e; omega
        rw [o₂ _ hne (inReg_ne (5 - m) (by omega)).1, in₁ m (by omega)]
    · rw [o₂ _ (Ne.symm hc) (by decide)]; exact c₁
    · rw [o₂ _ (Ne.symm hsp) (by decide)]; exact sp₁

/-! ## Outputs -/

/-- The output bit of S-box `j` that goes into scratch slot `k`, if any. -/
def outSlot (ρ : Role) (j k : Nat) : Option Nat :=
  if 8 ≤ k ∧ k < 72 then outIdx ρ j (k - 8) else none

def outPost (ρ : Role) (j : Nat) (e : Env Nat) : Bool :=
  (List.range 128).all fun k => e.slot k ==
    some (match outSlot ρ j k with
      | some i => 2 ^ k ^^^ 2 ^ (128 + i)
      | none => 2 ^ k)

theorem output_check : ∀ ρ : Role, ∀ j < 8,
    check (vars 64) varsCfg (fun _ => none) (outputCode ρ j) (varEnv outRegs) (outPost ρ j) = true := by
  intro ρ; cases ρ <;> decide +kernel

theorem outIdx_lt (ρ : Role) (j x i : Nat) (h : outIdx ρ j x = some i) : i < 4 := by
  have := List.mem_of_find?_eq_some h
  simpa using this

theorem outputCode_r15 : ∀ ρ : Role, ∀ j < 8,
    ((outputCode ρ j).all fun i => i.dst != some .r15) = true := by
  intro ρ; cases ρ <;> decide +kernel

theorem outputs_ok (ρ : Role) {j : Nat} (hj : j < 8) {s : State} (h : Room s) :
    ∃ s', runBlock isa (outputCode ρ j) s = some s' ∧
      (∀ k < 128, sl s' k = match outSlot ρ j k with
        | some i => sl s k ^^^ s.gpr (outReg i)
        | none => sl s k) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.gpr .rcx = s.gpr .rcx ∧ s'.gpr .rsp = s.gpr .rsp ∧
      s'.gpr .r15 = s.gpr .r15 ∧ Frame [scratchR s] s.mem s'.mem := by
  obtain ⟨e', s', hpost, hrun, p⟩ := varsRun outRegs (output_check ρ j hj) h
  simp only [outPost, List.all_eq_true, List.mem_range, beq_iff_eq] at hpost
  refine ⟨s', hrun, fun k hk => ?_, p.rd, p.wr, p.base, p.ext,
    p.other .r15 (by simp [outputCode_r15 ρ j hj]), p.frame⟩
  rw [varRel_slot p.rel hk (hpost k hk)]
  split
  · rename_i i hi
    have hi4 : i < 4 := by
      simp only [outSlot] at hi
      split at hi
      · exact outIdx_lt ρ j _ i hi
      · cases hi
    rw [xorSet_two_pow_xor (by simp [varN, outRegs]; omega) (by simp [varN, outRegs]; omega)]
    have e1 : ¬ 128 + i < 128 := by omega
    simp only [varVals, hk, ite_true, e1, ite_false, Nat.add_sub_cancel_left, outReg]
  · rw [xorSet_two_pow _ (by simp [varN]; omega)]
    simp only [varVals, hk, ite_true]

/-! ## One S-box -/

theorem sboxStep_ok (ρ : Role) {j : Nat} (hj : j < 8) {s : State} (h : Room s) (k : BitVec 48)
    (hkey : ∀ i < 6, (s.gpr .r15).getLsbD (58 + i) = k.getLsbD (inBit j i)) :
    ∃ s', runBlock isa (sboxStep ρ j) s = some s' ∧
      (∀ x < 64, words s' x = step ρ k j (words s) x) ∧
      (∀ x < 128, 72 ≤ x → sl s' x = sl s x) ∧ s'.gpr .r15 = s.gpr .r15 <<< 6 ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.gpr .rcx = s.gpr .rcx ∧ s'.gpr .rsp = s.gpr .rsp ∧
      Frame [scratchR s] s.mem s'.mem := by
  obtain ⟨s₁, run₁, k₁, in₁, c₁, sp₁, m₁, rd₁, wr₁⟩ := inputsN_ok ρ hj (Nat.le_refl 6) h
  have h₁ := h.congr c₁ wr₁
  have ok₁ : Ok sboxCfg s₁ :=
    Ok.of_region h₁.scratch rfl (by show 8 * spills ≤ 1024; decide) (by decide) rfl
  obtain ⟨s₂, run₂, out₂, rd₂, wr₂, c₂, sp₂, k₂, f₂⟩ := sbox_ok j hj ok₁
  have h₂ := h₁.congr c₂ wr₂
  obtain ⟨s₃, run₃, sl₃, rd₃, wr₃, c₃, sp₃, k₃, f₃⟩ := outputs_ok ρ hj h₂
  have sl₂ : ∀ x < 128, spills ≤ x → sl s₂ x = sl s x := by
    intro x hx hs
    rw [sl_of_spill c₂ (frame_of_spills f₂) hs hx]
    simp only [sl, m₁, c₁]
  have hin : ∀ i < 6, s₁.gpr (inReg i) =
      maskVal (k.getLsbD (inBit j i)) ^^^ sl s (stSlot (readWord ρ (eBit (inBit j i)))) := by
    intro i hi
    have e := in₁ (5 - i) (by omega)
    rw [show 5 - (5 - i) = i by omega] at e
    rw [e, show 63 - (5 - i) = 58 + i by omega, hkey i hi]
  refine ⟨s₃, ?_, fun x hx => ?_, fun x hx hl => ?_, ?_, rd₃.trans (rd₂.trans rd₁),
    wr₃.trans (wr₂.trans wr₁), c₃.trans (c₂.trans c₁), sp₃.trans (sp₂.trans sp₁), ?_⟩
  · rw [sboxStep, inputCode_eq]; exact runBlock_cat_some (runBlock_cat_some run₁ run₂) run₃
  · have hs : stSlot x < 128 := by unfold stSlot; omega
    have e₂ : sl s₂ (stSlot x) = words s x := sl₂ _ hs (by unfold stSlot spills; omega)
    have hos : outSlot ρ j (stSlot x) = outIdx ρ j x := by
      simp only [outSlot, stSlot, show 8 ≤ 8 + x ∧ 8 + x < 72 by omega, and_self, ite_true,
        Nat.add_sub_cancel_left]
    simp only [words]
    rw [sl₃ _ hs, hos]
    simp only [VG.Proof.TripleDes.Bitslice.step]
    rcases hidx : outIdx ρ j x with _ | i
    · exact e₂
    · have hi4 := outIdx_lt ρ j x i hidx
      dsimp only
      rw [e₂]
      congr 1
      apply BitVec.eq_of_getLsbD_eq
      intro p hp
      rw [out₂ i hi4 p hp]
      simp only [sboxOut, getLsbD_ofBits, hp, decide_true, Bool.true_and]
      congr 2
      apply BitVec.eq_of_getLsbD_eq
      intro i' hi'
      simp only [inputAt, sboxIn, getLsbD_ofBits, hi', decide_true, Bool.true_and, hin i' hi',
        BitVec.getLsbD_xor, getLsbD_mask _ hp, words]
      rw [Bool.xor_comm]
  · rw [sl₃ x hx]
    have : outSlot ρ j x = none := by
      simp only [outSlot, show ¬ (8 ≤ x ∧ x < 72) by omega, ite_false]
    rw [this]
    exact sl₂ x hx (by unfold spills; omega)
  · rw [k₃, k₂, k₁]
  · have g₁ : Frame [scratchR s] s.mem s₁.mem := by rw [m₁]; exact Frame.refl _ _
    have g₂ : Frame [scratchR s] s₁.mem s₂.mem := by
      have := spill_toScratch (frame_of_spills f₂)
      rwa [show scratchR s₁ = scratchR s by simp only [scratchR, c₁]] at this
    rw [show scratchR s₂ = scratchR s by simp only [scratchR, c₂, c₁]] at f₃
    exact g₁.trans (g₂.trans f₃)

/-! ## The exchange of the halves -/

/-- The slot whose word goes into slot `k`. -/
def swapSlot (k : Nat) : Nat :=
  if 8 ≤ k ∧ k < 72 then (match partner (k - 8) with | some y => 8 + y | none => k) else k

def swapPost (e : Env Nat) : Bool :=
  (List.range 128).all fun k => e.slot k == some (2 ^ swapSlot k)

theorem swap_check :
    check (vars 64) varsCfg (fun _ => none) swapHalves (varEnv []) swapPost = true := by
  decide +kernel

theorem swapSlot_lt : ∀ k < 128, swapSlot k < 128 := by decide +kernel

theorem swapHalves_ok {s : State} (h : Room s) :
    ∃ s', runBlock isa swapHalves s = some s' ∧ (∀ x < 64, words s' x = swapW (words s) x) ∧
      (∀ x < 128, 72 ≤ x → sl s' x = sl s x) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.gpr .rcx = s.gpr .rcx ∧ s'.gpr .rsp = s.gpr .rsp ∧
      Frame [scratchR s] s.mem s'.mem := by
  obtain ⟨e', s', hpost, hrun, p⟩ := varsRun [] swap_check h
  simp only [swapPost, List.all_eq_true, List.mem_range, beq_iff_eq] at hpost
  have key : ∀ k < 128, sl s' k = sl s (swapSlot k) := by
    intro k hk
    rw [varRel_slot p.rel hk (hpost k hk), xorSet_two_pow _ (by simp [varN]; exact swapSlot_lt k hk)]
    simp only [varVals, swapSlot_lt k hk, ite_true]
  refine ⟨s', hrun, fun x hx => ?_, fun x hx hl => ?_, p.rd, p.wr, p.base, p.ext, p.frame⟩
  · simp only [words, stSlot]
    rw [key _ (by omega)]
    simp only [swapW, swapSlot, show 8 ≤ 8 + x ∧ 8 + x < 72 by omega, and_self, ite_true,
      Nat.add_sub_cancel_left]
    rcases partner x with _ | y <;> rfl
  · rw [key x hx]
    simp only [swapSlot, show ¬ (8 ≤ x ∧ x < 72) by omega, ite_false]

end VG.Proof.TripleDes.X86_64.Bitsliced
