import VerifiedGarbage.Proof.TripleDes.AArch64.Bitsliced.Sbox
import VerifiedGarbage.Proof.TripleDes.Bitslice.Tdea

/-!
# One S-box of an AdvSIMD round, and the exchange of the halves

`sboxStep_ok`: the code of S-box `j` (its inputs, each the key bit of the
broadcast round key in `v30` as a mask, XORed with the word of `E`; its
circuit; XORing its outputs into their words) does to the state words what
`step` does with the round key's low 48 bits. `swapHalves_ok`: the
exchange of the halves does what `swapW` does.
-/

namespace VG.Proof.TripleDes.AArch64.BitslicedNeon

open VG VG.AArch64 VG.AArch64.StraightV VG.AArch64.RegUpd VG.Bitslice
open VG.Impl.TripleDes.AArch64.BitsliceNeon VG.Impl.TripleDes.Bitslice
open VG.Proof.TripleDes.Bitslice (step sboxIn sboxOut outIdx partner swapW)

theorem word_in {s : State} (h : Room s) {w : Nat} (hw : w < 64) :
    InRegions (s.rd ++ s.wr) (vAddr (s.gpr .x4) w) 16 := by
  obtain ⟨r, hr, hc⟩ := h.slotIn w hw
  exact ⟨r, List.mem_append_right _ hr, hc⟩

theorem exec_vop (s : State) (op : VOp) :
    exec (.vop op) s = (op.eval s).map fun (d, x) => s.setV d x := rfl

/-- `0 - ((K <<< (63 - b)) >>> 63)`: bit `b` of `K` as a mask. -/
theorem bitMask (K : BitVec 64) {b : Nat} (hb : b < 64) :
    0 - ((K <<< (63 - b)) >>> 63) = if K.getLsbD b then BitVec.allOnes 64 else 0 := by
  have h : (K <<< (63 - b)) >>> 63 = if K.getLsbD b then 1 else 0 := by
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_ushiftRight, BitVec.getLsbD_shiftLeft]
    by_cases h0 : i = 0
    · subst h0
      simp only [Nat.add_zero, show (63 : Nat) < 64 by decide, decide_true, Bool.true_and,
        show ¬ (63 < 63 - b) by omega, decide_false, Bool.not_false, show 63 - (63 - b) = b by omega]
      split <;> simp_all
    · simp only [show ¬ (63 + i < 64) by omega, decide_false, Bool.false_and]
      split <;> simp [BitVec.getLsbD_one, h0]
  rw [h]
  split <;> simp

theorem vdword_maskX (c : Bool) {q : Nat} (hq : q < 2) :
    vdword (maskX c) q = if c then BitVec.allOnes 64 else 0 := by
  cases c
  · simp only [maskX, Bool.false_eq_true, ite_false]; exact vdword_zero q
  · apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [maskX, ite_true, vdword, BitVec.getLsbD_extractLsb', BitVec.getLsbD_allOnes, hi,
      decide_true, Bool.true_and, show 64 * q + i < 128 by omega]

/-- The facts the code of an S-box needs: the round key broadcast in `v30`
and zero in `v31`. -/
structure KeyRegs (K : BitVec 64) (s : State) : Prop where
  key : s.v keyReg = ofVDwords K K
  zero : s.v zeroReg = 0

theorem KeyRegs.congr {K : BitVec 64} {s s' : State} (h : KeyRegs K s)
    (hk : s'.v keyReg = s.v keyReg) (hz : s'.v zeroReg = s.v zeroReg) : KeyRegs K s' :=
  ⟨hk.trans h.key, hz.trans h.zero⟩

/-! ## Inputs -/

theorem inReg_ne : ∀ i < 6, inReg i ≠ keyReg ∧ inReg i ≠ zeroReg ∧ inReg i ≠ tmpReg := by decide

theorem inReg_inj' : ∀ a < 6, ∀ b < 6, inReg a = inReg b → a = b := by decide

/-- One input: key bit `b` as a mask, XORed with state word `w`. -/
theorem inputStep_run {K : BitVec 64} {s : State} (h : Room s) (hk : KeyRegs K s) {x : VReg}
    (hx : x ≠ keyReg ∧ x ≠ zeroReg ∧ x ≠ tmpReg) {w b : Nat} (hw : w < 64) (hb : b < 64) :
    ∃ s', runBlock isa [.vop (.shift .shl .d2 x keyReg (63 - b)),
        .vop (.shift .ushr .d2 x x 63), .vop (.sub .d2 x zeroReg x),
        .ldrq tmpReg .x4 (16 * w), .vop (.logic .eor x x tmpReg)] s = some s' ∧
      s'.v x = words s w ^^^ maskX (K.getLsbD b) ∧
      (∀ y, y ≠ x → y ≠ tmpReg → s'.v y = s.v y) ∧
      s'.gpr = s.gpr ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ s'.c = s.c := by
  obtain ⟨hxk, hxz, hxt⟩ := hx
  let v₁ := VArr.d2.map2 (fun w a b' => VShiftOp.shl.eval (63 - b) w a b') (s.v x) (s.v keyReg)
  let s₁ := s.setV x v₁
  have e₁ : exec (.vop (.shift .shl .d2 x keyReg (63 - b))) s = some s₁ := by
    rw [exec_vop]; simp only [VOp.eval, VArr.esize, VShiftOp.ok, show 63 - b < 64 by omega,
      decide_true, ite_true, Option.map_some]; rfl
  let v₂ := VArr.d2.map2 (fun w a b' => VShiftOp.ushr.eval 63 w a b') (s₁.v x) (s₁.v x)
  let s₂ := s₁.setV x v₂
  have e₂ : exec (.vop (.shift .ushr .d2 x x 63)) s₁ = some s₂ := by
    rw [exec_vop]; simp only [VOp.eval, VArr.esize, VShiftOp.ok]; rfl
  let v₃ := VArr.d2.map2 (fun _ a b' => a - b') (s₂.v zeroReg) (s₂.v x)
  let s₃ := s₂.setV x v₃
  have e₃ : exec (.vop (.sub .d2 x zeroReg x)) s₂ = some s₃ := rfl
  have hin : InRegions (s₃.rd ++ s₃.wr) (vAddr (s₃.gpr .x4) w) 16 := word_in h hw
  let s₄ := s₃.setV tmpReg (s₃.mem.readW (vAddr (s₃.gpr .x4) w) 128)
  have e₄ : exec (.ldrq tmpReg .x4 (16 * w)) s₃ = some s₄ := by
    simp only [exec, addr_slot (show 16 * w < 65536 by omega), Option.bind_some, State.load, hin,
      ite_true, Option.map_some, read16_readW]
    rfl
  let s₅ := s₄.setV x (s₄.v x ^^^ s₄.v tmpReg)
  have e₅ : exec (.vop (.logic .eor x x tmpReg)) s₄ = some s₅ := rfl
  refine ⟨s₅, ?_, ?_, fun y h1 h2 => ?_, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · rw [runBlock_cons, e₁, runStep_some, runBlock_cons, e₂, runStep_some, runBlock_cons, e₃,
      runStep_some, runBlock_cons, e₄, runStep_some, runBlock_cons, e₅, runStep_some, runBlock_nil]
  · have hv₁ : ∀ q < 2, vdword v₁ q = K <<< (63 - b) := by
      intro q hq
      simp only [v₁, vdword_map2 _ _ _ hq, VShiftOp.eval, hk.key, vdword_dwords _ _ hq, ite_self]
    have hv₂ : ∀ q < 2, vdword v₂ q = (K <<< (63 - b)) >>> 63 := by
      intro q hq
      simp only [v₂, s₁, v_setV_self, vdword_map2 _ _ _ hq, VShiftOp.eval, hv₁ q hq]
    have zx : s₂.v zeroReg = 0 := by
      simp only [s₂, s₁, v_setV_of_ne _ _ (Ne.symm hxz), hk.zero]
    have hv₃ : ∀ q < 2, vdword v₃ q = 0 - ((K <<< (63 - b)) >>> 63) := by
      intro q hq
      simp only [v₃, vdword_map2 _ _ _ hq, zx, vdword_zero, s₂, v_setV_self, hv₂ q hq]
      rfl
    have e : s₅.v x = v₃ ^^^ s.mem.readW (vAddr (s.gpr .x4) w) 128 := by
      simp only [s₅, s₄, s₃, v_setV_self, v_setV_of_ne _ _ hxt]
      rfl
    apply eq_of_vdword; intro q hq
    rw [e, vdword_xor, hv₃ q hq, bitMask K hb, vdword_xor, vdword_maskX _ hq, BitVec.xor_comm]
    rfl
  · simp only [s₅, s₄, s₃, s₂, s₁, v_setV_of_ne _ _ h1, v_setV_of_ne _ _ h2]

def inputsN (ρ : Role) (j n : Nat) : List Instr := (List.range n).flatMap (inputStep ρ j)

theorem inputCode_eq (ρ : Role) (j : Nat) : inputCode ρ j = inputsN ρ j 6 := rfl

theorem inputsN_succ (ρ : Role) (j n : Nat) :
    inputsN ρ j (n + 1) = inputsN ρ j n ++ inputStep ρ j n := by
  simp only [inputsN, List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
    List.append_nil]

theorem readWord_lt : ∀ ρ : Role, ∀ j < 8, ∀ i < 6, readWord ρ (eBit (inBit j i)) < 64 := by
  intro ρ; cases ρ <;> decide +kernel

theorem inBit_lt' : ∀ j < 8, ∀ i < 6, inBit j i < 64 := by decide

theorem inputsN_ok (ρ : Role) {j : Nat} (hj : j < 8) {n : Nat} (hn : n ≤ 6) {K : BitVec 64}
    {s : State} (h : Room s) (hk : KeyRegs K s) :
    ∃ s', runBlock isa (inputsN ρ j n) s = some s' ∧
      (∀ m < n, s'.v (inReg m) = words s (readWord ρ (eBit (inBit j m))) ^^^
        maskX (K.getLsbD (inBit j m))) ∧
      KeyRegs K s' ∧ s'.gpr = s.gpr ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      s'.sp = s.sp ∧ s'.c = s.c := by
  induction n with
  | zero => exact ⟨s, runBlock_nil, fun m hm => by omega, hk, rfl, rfl, rfl, rfl, rfl, rfl⟩
  | succ n ih =>
    obtain ⟨s₁, run₁, in₁, k₁, g₁, m₁, rd₁, wr₁, sp₁, c₁⟩ := ih (by omega)
    have h₁ : Room s₁ := room_congr h (by rw [g₁]) wr₁
    obtain ⟨hxk, hxz, hxt⟩ := inReg_ne n (by omega)
    obtain ⟨s₂, run₂, q₂, y₂, g₂, m₂, rd₂, wr₂, sp₂, c₂⟩ :=
      inputStep_run h₁ k₁ ⟨hxk, hxz, hxt⟩ (w := readWord ρ (eBit (inBit j n)))
        (readWord_lt ρ j hj _ (by omega)) (inBit_lt' j hj n (by omega))
    refine ⟨s₂, ?_, fun m hm => ?_, k₁.congr (y₂ _ (Ne.symm hxk) (by decide))
        (y₂ _ (Ne.symm hxz) (by decide)), g₂.trans g₁, m₂.trans m₁, rd₂.trans rd₁, wr₂.trans wr₁,
      sp₂.trans sp₁, c₂.trans c₁⟩
    · rw [inputsN_succ]; exact runBlock_cat_some run₁ run₂
    · by_cases he : m = n
      · subst he
        rw [q₂]
        simp only [words, m₁, g₁]
      · have hne : inReg m ≠ inReg n := by
          intro e; have := inReg_inj' _ (by omega) _ (by omega) e; omega
        rw [y₂ _ hne (inReg_ne m (by omega)).2.2, in₁ m (by omega)]

/-! ## Outputs -/

def outPost (ρ : Role) (j : Nat) (e : Env Nat) : Bool :=
  (List.range 64).all fun k => e.slot k ==
    some (match outIdx ρ j k with
      | some i => 2 ^ k ^^^ 2 ^ (64 + i)
      | none => 2 ^ k)

/-- The output registers of S-box `j`. -/
def outRegs (j : Nat) : List VReg := (List.range 4).map (outReg j)

theorem output_check : ∀ ρ : Role, ∀ j < 8,
    check (vars 64) stateCfg (outputCode ρ j) (varEnv (outRegs j)) (outPost ρ j) = true := by
  intro ρ; cases ρ <;> lit_decide

theorem outIdx_lt (ρ : Role) (j x i : Nat) (h : outIdx ρ j x = some i) : i < 4 := by
  have := List.mem_of_find?_eq_some h
  simpa using this

theorem outputCode_regs : ∀ ρ : Role, ∀ j < 8,
    ((outputCode ρ j).all fun i => dstOf i == none && vdstOf i != some keyReg &&
      vdstOf i != some zeroReg) = true := by
  intro ρ; cases ρ <;> lit_decide

theorem outRegs_getD (j : Nat) {i : Nat} (hi : i < 4) : (outRegs j).getD i .v0 = outReg j i := by
  simp [outRegs, List.getD_eq_getElem?_getD, hi]

theorem outputs_ok (ρ : Role) {j : Nat} (hj : j < 8) {s : State} (h : Room s) :
    ∃ s', runBlock isa (outputCode ρ j) s = some s' ∧
      (∀ k < 64, words s' k = match outIdx ρ j k with
        | some i => words s k ^^^ s.v (outReg j i)
        | none => words s k) ∧
      s'.gpr = s.gpr ∧ s'.v keyReg = s.v keyReg ∧ s'.v zeroReg = s.v zeroReg ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ s'.c = s.c ∧
      Frame [stateR s] s.mem s'.mem := by
  obtain ⟨e', s', hpost, hrun, p⟩ := varsRun (outRegs j) (output_check ρ j hj) h
  simp only [outPost, List.all_eq_true, List.mem_range, beq_iff_eq] at hpost
  have regs := List.all_eq_true.mp (outputCode_regs ρ j hj)
  have noV : ∀ r, (r = keyReg ∨ r = zeroReg) →
      ¬ ((outputCode ρ j).all fun op => vdstOf op != some r) = false := by
    intro r hr
    simp only [Bool.not_eq_false, List.all_eq_true, bne_iff_ne, ne_eq]
    intro op hop h'
    have := regs op hop
    rcases hr with rfl | rfl <;> simp [h'] at this
  refine ⟨s', hrun, fun k hk => ?_, funext fun r => p.gpr r (by
      simp only [Bool.not_eq_false, List.all_eq_true, bne_iff_ne, ne_eq]
      intro op hop h'
      have := regs op hop
      simp [h'] at this),
    p.other _ (noV _ (Or.inl rfl)), p.other _ (noV _ (Or.inr rfl)), p.rd, p.wr, p.sp, p.carry,
    p.frame⟩
  apply eq_of_vdword; intro q hq
  have hs := p.rel.slot k _ hk (hpost k hk) q hq
  simp only [VarRel] at hs
  have e : vdword (words s' k) q = vdword (s'.mem.readW (vAddr (s'.gpr stateCfg.base) k) 128) q := by
    simp only [words, stateCfg]
  rw [e, hs]
  split
  · rename_i i hi
    have hi4 := outIdx_lt ρ j k i hi
    rw [xorSet_two_pow_xor (by simp [varN, outRegs]; omega) (by simp [varN, outRegs]; omega)]
    simp only [varVals, hk, ite_true, show ¬ 64 + i < 64 by omega, ite_false,
      Nat.add_sub_cancel_left, vdword_xor, laneW, outRegs_getD j hi4]
  · rw [xorSet_two_pow _ (by simp [varN]; omega)]
    simp only [varVals, hk, ite_true, laneW]

/-! ## One S-box -/

theorem sboxStep_ok (ρ : Role) {j : Nat} (hj : j < 8) {K : BitVec 64} {s : State} (h : Room s)
    (hk : KeyRegs K s) :
    ∃ s', runBlock isa (sboxStep ρ j) s = some s' ∧
      (∀ x < 64, words s' x = step ρ (K.setWidth 48) j (words s) x) ∧
      KeyRegs K s' ∧ s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ s'.c = s.c ∧
      Frame [stateR s] s.mem s'.mem := by
  obtain ⟨s₁, run₁, in₁, k₁, g₁, m₁, rd₁, wr₁, sp₁, c₁⟩ := inputsN_ok ρ hj (Nat.le_refl 6) h hk
  obtain ⟨s₂, run₂, out₂, g₂, c₂, sp₂, rd₂, wr₂, kk₂, kz₂, m₂⟩ := sbox_ok j hj s₁
  have h₂ : Room s₂ := room_congr h (by rw [g₂, g₁]) (wr₂.trans wr₁)
  obtain ⟨s₃, run₃, w₃, g₃, kk₃, kz₃, rd₃, wr₃, sp₃, c₃, f₃⟩ := outputs_ok ρ hj h₂
  have w₂ : ∀ x, words s₂ x = words s x := fun x => by simp only [words, m₂, m₁, g₂, g₁]
  have hin : ∀ i < 6, s₁.v (inReg i) =
      words s (readWord ρ (eBit (inBit j i))) ^^^ maskX ((K.setWidth 48).getLsbD (inBit j i)) := by
    intro i hi
    rw [in₁ i hi, BitVec.getLsbD_setWidth]
    simp [VG.Proof.TripleDes.Bitslice.inBit_lt j hj i hi]
  refine ⟨s₃, ?_, fun x hx => ?_, k₁.congr (kk₃.trans kk₂) (kz₃.trans kz₂), g₃.trans (g₂.trans g₁),
    rd₃.trans (rd₂.trans rd₁), wr₃.trans (wr₂.trans wr₁), sp₃.trans (sp₂.trans sp₁),
    c₃.trans (c₂.trans c₁), ?_⟩
  · rw [sboxStep, inputCode_eq]; exact runBlock_cat_some (runBlock_cat_some run₁ run₂) run₃
  · rw [w₃ x hx]
    simp only [VG.Proof.TripleDes.Bitslice.step]
    rcases hidx : outIdx ρ j x with _ | i
    · exact w₂ x
    · have hi4 := outIdx_lt ρ j x i hidx
      dsimp only
      rw [w₂ x]
      refine congrArg (words s x ^^^ ·) ?_
      apply BitVec.eq_of_getLsbD_eq
      intro p hp
      rw [out₂ i hi4 p hp]
      simp only [sboxOut, getLsbD_ofBits, hp, decide_true, Bool.true_and]
      refine congrArg (fun z => (Spec.TripleDes.sBox j z).getLsbD i) ?_
      apply BitVec.eq_of_getLsbD_eq
      intro i' hi'
      simp only [inputAt, sboxIn, getLsbD_ofBits, hi', decide_true, Bool.true_and, hin i' hi',
        BitVec.getLsbD_xor, getLsbD_maskX _ hp]
  · have e : stateR s₂ = stateR s := by simp only [stateR, g₂, g₁]
    rw [e, m₂, m₁] at f₃
    exact f₃

/-! ## The exchange of the halves -/

/-- The word that goes into word `k`. -/
def swapSlot (k : Nat) : Nat := match partner k with | some y => y | none => k

def swapPost (e : Env Nat) : Bool :=
  (List.range 64).all fun k => e.slot k == some (2 ^ swapSlot k)

theorem swap_check : check (vars 64) stateCfg swapHalves (varEnv [.v0, .v1]) swapPost = true := by
  decide +kernel

theorem swapSlot_lt : ∀ k < 64, swapSlot k < 64 := by decide +kernel

theorem swap_regs : (swapHalves.all fun i => dstOf i == none && vdstOf i != some keyReg &&
    vdstOf i != some zeroReg) = true := by
  decide +kernel

theorem swapHalves_ok {s : State} (h : Room s) :
    ∃ s', runBlock isa swapHalves s = some s' ∧ (∀ x < 64, words s' x = swapW (words s) x) ∧
      s'.gpr = s.gpr ∧ s'.v keyReg = s.v keyReg ∧ s'.v zeroReg = s.v zeroReg ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ s'.c = s.c ∧
      Frame [stateR s] s.mem s'.mem := by
  obtain ⟨e', s', hpost, hrun, p⟩ := varsRun [.v0, .v1] swap_check h
  simp only [swapPost, List.all_eq_true, List.mem_range, beq_iff_eq] at hpost
  have regs := List.all_eq_true.mp swap_regs
  have noV : ∀ r, (r = keyReg ∨ r = zeroReg) →
      ¬ (swapHalves.all fun op => vdstOf op != some r) = false := by
    intro r hr
    simp only [Bool.not_eq_false, List.all_eq_true, bne_iff_ne, ne_eq]
    intro op hop h'
    have := regs op hop
    rcases hr with rfl | rfl <;> simp [h'] at this
  refine ⟨s', hrun, fun x hx => ?_, funext fun r => p.gpr r (by
      simp only [Bool.not_eq_false, List.all_eq_true, bne_iff_ne, ne_eq]
      intro op hop h'
      have := regs op hop
      simp [h'] at this),
    p.other _ (noV _ (Or.inl rfl)), p.other _ (noV _ (Or.inr rfl)), p.rd, p.wr, p.sp, p.carry,
    p.frame⟩
  apply eq_of_vdword; intro q hq
  have hs := p.rel.slot x _ hx (hpost x hx) q hq
  simp only [VarRel] at hs
  have e : vdword (words s' x) q = vdword (s'.mem.readW (vAddr (s'.gpr stateCfg.base) x) 128) q := by
    simp only [words, stateCfg]
  rw [e, hs, xorSet_two_pow _ (by simp [varN]; have := swapSlot_lt x hx; omega)]
  simp only [varVals, swapSlot_lt x hx, ite_true, laneW]
  unfold swapW swapSlot
  cases partner x <;> rfl

end VG.Proof.TripleDes.AArch64.BitslicedNeon
