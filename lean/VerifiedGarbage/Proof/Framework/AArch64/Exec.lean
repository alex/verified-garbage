import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.Bswap
import VerifiedGarbage.TCB.AArch64.Isa
import VerifiedGarbage.Proof.Framework.Block

/-!
# AArch64: instruction-level rewrite lemmas for symbolic execution
-/

namespace VG.AArch64

theorem exec_ldr_w {s : State} {t n : Reg} {off : Nat} (ho : off % 4 = 0 ∧ off < 16384)
    (h : InRegions (s.rd ++ s.wr) (s.gpr n + BitVec.ofNat 64 off) 4) :
    exec (.ldr .w t n off) s = some (s.write .w t (s.mem.readW (s.gpr n + BitVec.ofNat 64 off) 32)) := by
  simp only [exec, addr, Size.bytes, ho, and_self, ite_true, Option.bind_some, State.load, h,
    Option.map_some, Mem.readW]

theorem exec_str_w {s : State} {t n : Reg} {off : Nat} (ho : off % 4 = 0 ∧ off < 16384)
    (h : InRegions s.wr (s.gpr n + BitVec.ofNat 64 off) 4) :
    exec (.str .w t n off) s =
      some { s with mem := s.mem.writeW (s.gpr n + BitVec.ofNat 64 off) ((s.gpr t).setWidth 32) } := by
  simp only [exec, addr, Size.bytes, ho, and_self, ite_true, Option.bind_some, State.store, h,
    Mem.writeW]
  rfl

theorem exec_movz_w {s : State} {d : Reg} {imm : BitVec 16} :
    exec (.movz .w d imm 0) s = some (s.write .w d (imm.setWidth 32)) := by
  simp only [exec, Size.bits, Nat.mul_zero, show (0 : Nat) < 32 from by decide, ite_true]
  exact congrArg (fun v => some (s.write .w d v)) (BitVec.shiftLeft_zero _)

theorem exec_movk_w {s : State} {d : Reg} {imm : BitVec 16} :
    exec (.movk .w d imm 1) s =
      some (s.write .w d ((s.gpr d).setWidth 32 &&& (0xFFFF : BitVec 32) ||| imm.setWidth 32 <<< 16 :
        BitVec 32)) := by
  simp [exec, Size.bits, State.read]

theorem testBit_65535 (i : Nat) : Nat.testBit 65535 i = decide (i < 16) :=
  Nat.testBit_two_pow_sub_one 16 i

/-- `movz` of the low half then `movk` of the high half builds the word. -/
theorem movz_movk (x : BitVec 32) :
    (x.extractLsb' 0 16).setWidth 32 &&& 0xFFFF ||| (x.extractLsb' 16 16).setWidth 32 <<< 16 = x := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth,
    BitVec.getLsbD_extractLsb', BitVec.natCast_eq_ofNat,
    BitVec.getLsbD_ofNat, testBit_65535, hi, decide_true, Bool.true_and, Nat.zero_add]
  rcases (by omega : i < 16 ∨ 16 ≤ i) with h | h <;>
  simp (disch := omega) only [decide_eq_true, decide_eq_false, Bool.true_and, Bool.false_and,
    Bool.and_false, Bool.or_false, Bool.false_or, Bool.not_false, Bool.not_true, Bool.and_true]
  all_goals exact congrArg _ (by omega)

theorem exec_add {sz : Size} {s : State} {d n m : Reg} :
    exec (.add sz d n m) s = some (s.write sz d (s.read sz n + s.read sz m)) := rfl

theorem exec_logic {op : LogicOp} {sz : Size} {s : State} {d n m : Reg} :
    exec (.logic op sz d n m) s = some (s.write sz d (match op with
      | .and => s.read sz n &&& s.read sz m | .orr => s.read sz n ||| s.read sz m
      | .eor => s.read sz n ^^^ s.read sz m)) := rfl

theorem exec_logicRor {op : LogicOp} {sz : Size} {s : State} {d n m : Reg} {sh : Nat}
    (h : sh < sz.bits) :
    exec (.logicRor op sz d n m sh) s = some (s.write sz d (match op with
      | .and => s.read sz n &&& (s.read sz m).rotateRight sh
      | .orr => s.read sz n ||| (s.read sz m).rotateRight sh
      | .eor => s.read sz n ^^^ (s.read sz m).rotateRight sh)) := by
  simp only [exec, h, ite_true]
  rfl

theorem exec_bicRor {sz : Size} {s : State} {d n m : Reg} {sh : Nat}
    (h : sh < sz.bits) :
    exec (.bicRor sz d n m sh) s =
      some (s.write sz d (s.read sz n &&& ~~~((s.read sz m).rotateRight sh))) := by
  simp only [exec, h, ite_true]

theorem exec_ror_w {s : State} {d n : Reg} {sh : Nat} (h : sh < 32) :
    exec (.ror .w d n sh) s = some (s.write .w d ((s.read .w n).rotateRight sh)) := by
  simp [exec, Size.bits, h]

theorem exec_lsr_w {s : State} {d n : Reg} {sh : Nat} (h : sh < 32) :
    exec (.lsr .w d n sh) s = some (s.write .w d (s.read .w n >>> sh)) := by
  simp [exec, Size.bits, h]

theorem exec_rev32 {s : State} {d n : Reg} :
    exec (.rev32 d n) s = some (s.write .w d (rev32 (s.read .w n))) := rfl

theorem exec_addImm_x {s : State} {d n : Reg} {imm : Nat} (h : imm < 4096) :
    exec (.addImm .x d n imm) s = some (s.write .x d (s.read .x n + BitVec.ofNat _ imm)) := by
  simp [exec, h]

theorem exec_subImm_x {s : State} {d n : Reg} {imm : Nat} (h : imm < 4096) :
    exec (.subImm .x d n imm) s = some (s.write .x d (s.read .x n - BitVec.ofNat _ imm)) := by
  simp [exec, h]

/-- `movz` of the low half then `movk` of the high half, as the symbolic
execution leaves them. -/
theorem movz_movk' (x : BitVec 32) :
    (x.extractLsb' 0 16).setWidth 32 <<< (16 * 0) &&& ~~~((65535 : BitVec 32) <<< (16 * 1)) |||
      (x.extractLsb' 16 16).setWidth 32 <<< (16 * 1) = x := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth,
    BitVec.getLsbD_extractLsb', BitVec.getLsbD_not, BitVec.ofNat_eq_ofNat,
    BitVec.getLsbD_ofNat, testBit_65535, hi, decide_true, Bool.true_and, Nat.zero_add,
    Nat.reduceMul, Nat.sub_zero]
  rcases (by omega : i < 16 ∨ 16 ≤ i) with h | h <;>
  simp (disch := omega) only [decide_eq_true, decide_eq_false, Bool.true_and, Bool.false_and,
    Bool.and_false, Bool.or_false, Bool.false_or, Bool.not_false, Bool.not_true, Bool.and_true]
  all_goals exact congrArg _ (by omega)

theorem rev32_readW (m : Mem) (a : Addr) :
    rev32 (m.readW a 32) = (m a ++ m (a + 1) ++ m (a + 1 + 1) ++ m (a + 1 + 1 + 1) : BitVec 32) :=
  byteRev32_readW m a

theorem exec_ldr_x {s : State} {t n : Reg} {off : Nat} (ho : off % 8 = 0 ∧ off < 32768)
    (h : InRegions (s.rd ++ s.wr) (s.gpr n + BitVec.ofNat 64 off) 8) :
    exec (.ldr .x t n off) s = some (s.write .x t (s.mem.readW (s.gpr n + BitVec.ofNat 64 off) 64)) := by
  simp only [exec, addr, Size.bytes, ho, and_self, ite_true, Option.bind_some, State.load, h,
    Option.map_some, Mem.readW]

theorem exec_str_x {s : State} {t n : Reg} {off : Nat} (ho : off % 8 = 0 ∧ off < 32768)
    (h : InRegions s.wr (s.gpr n + BitVec.ofNat 64 off) 8) :
    exec (.str .x t n off) s =
      some { s with mem := s.mem.writeW (s.gpr n + BitVec.ofNat 64 off) (s.gpr t) } := by
  simp only [exec, addr, Size.bytes, ho, and_self, ite_true, Option.bind_some, State.store, h,
    Mem.writeW]
  rfl

theorem exec_ror_x {s : State} {d n : Reg} {sh : Nat} (h : sh < 64) :
    exec (.ror .x d n sh) s = some (s.write .x d ((s.read .x n).rotateRight sh)) := by
  simp [exec, Size.bits, h]

theorem exec_lsr_x {s : State} {d n : Reg} {sh : Nat} (h : sh < 64) :
    exec (.lsr .x d n sh) s = some (s.write .x d (s.read .x n >>> sh)) := by
  simp [exec, Size.bits, h]

theorem exec_rev {s : State} {d n : Reg} :
    exec (.rev d n) s = some (s.write .x d (rev64 (s.read .x n))) := rfl

/-- `movz` then three `movk`s, as the symbolic execution leaves them, build the
64-bit word. -/
theorem movz_movk64' (x : BitVec 64) :
    (((x.extractLsb' 0 16).setWidth 64 <<< (16 * 0) &&& ~~~((65535 : BitVec 64) <<< (16 * 1)) |||
      (x.extractLsb' 16 16).setWidth 64 <<< (16 * 1)) &&& ~~~((65535 : BitVec 64) <<< (16 * 2)) |||
      (x.extractLsb' 32 16).setWidth 64 <<< (16 * 2)) &&& ~~~((65535 : BitVec 64) <<< (16 * 3)) |||
      (x.extractLsb' 48 16).setWidth 64 <<< (16 * 3) = x := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth,
    BitVec.getLsbD_extractLsb', BitVec.getLsbD_not, BitVec.ofNat_eq_ofNat,
    BitVec.getLsbD_ofNat, testBit_65535, hi, decide_true, Bool.true_and, Nat.zero_add,
    Nat.reduceMul, Nat.sub_zero]
  rcases (by omega : i < 16 ∨ (16 ≤ i ∧ i < 32) ∨ (32 ≤ i ∧ i < 48) ∨ 48 ≤ i) with h | h | h | h <;>
  simp (disch := omega) only [decide_eq_true, decide_eq_false, Bool.true_and, Bool.false_and,
    Bool.and_false, Bool.or_false, Bool.false_or, Bool.not_false, Bool.not_true, Bool.and_true] <;>
  exact congrArg _ (by omega)

/-- A 64-bit load followed by `rev` reads the eight bytes big-endian. -/
theorem rev64_readW (m : Mem) (a : Addr) :
    rev64 (m.readW a 64) = (m a ++ m (a + 1) ++ m (a + 1 + 1) ++ m (a + 1 + 1 + 1) ++
      m (a + 1 + 1 + 1 + 1) ++ m (a + 1 + 1 + 1 + 1 + 1) ++ m (a + 1 + 1 + 1 + 1 + 1 + 1) ++
      m (a + 1 + 1 + 1 + 1 + 1 + 1 + 1) : BitVec 64) :=
  byteRev64_readW m a

end VG.AArch64

namespace VG.AArch64

theorem exec_sp {i : Instr} {s s' : State} (h : exec i s = some s') : s'.sp = s.sp := by
  cases i
  case ldrSp =>
    simp only [exec] at h
    split at h <;> [skip; cases h]
    obtain ⟨_, _, rfl⟩ := Option.map_eq_some_iff.mp h; rfl
  all_goals
  simp only [exec, Option.bind_eq_some_iff, Option.map_eq_some_iff, State.write, State.load,
    State.store] at h <;>
  (repeat' split at h) <;>
  (try simp only [Option.some.injEq, reduceCtorEq] at h) <;>
  first
  | (subst h; rfl)
  | (obtain ⟨_, _, _, _, rfl⟩ := h; rfl)
  | (obtain ⟨_, _, h⟩ := h; split at h <;> simp only [Option.some.injEq, reduceCtorEq] at h;
     subst h; rfl)

theorem execBlock_sp {is : List Instr} {s s' : State} {t : List Leak}
    (h : VG.execBlock isa is s = some (s', t)) : s'.sp = s.sp := by
  induction is generalizing s t with
  | nil => simp only [VG.execBlock, Option.some.injEq, Prod.mk.injEq] at h; rw [h.1]
  | cons i is ih =>
    simp only [VG.execBlock] at h
    split at h
    · cases h
    · rename_i s₁ he
      simp only [Option.map_eq_some_iff, Prod.exists] at h
      obtain ⟨s₂, _, h, he'⟩ := h
      simp only [Prod.mk.injEq] at he'
      obtain ⟨rfl, -⟩ := he'
      rw [ih h]; exact exec_sp he

/-- Opening a frame subtracts its region's size from SP. -/
theorem push_sp {i : Instr} {s s₁ : State} (h : push i s = some s₁) :
    ∃ n, s₁.wr.head? = some ⟨s₁.sp, n⟩ ∧ s₁.sp = s.sp - BitVec.ofNat 64 n := by
  cases i <;> simp only [push, reduceCtorEq] at h
  all_goals split at h <;> cases h
  all_goals exact ⟨_, rfl, rfl⟩

/-- Closing a frame adds back exactly its region's size. -/
theorem pop_sp {j : Instr} {s₁ s₂ s' : State} (h : pop j s₁ s₂ = some s') :
    s₂.sp = s₁.sp ∧ ∀ n, s₁.wr.head? = some ⟨s₁.sp, n⟩ →
      s'.sp = s₂.sp + BitVec.ofNat 64 n := by
  cases j <;> simp only [pop, reduceCtorEq] at h
  all_goals split at h <;> cases h
  case pop r hc =>
    refine ⟨hc.1, fun n hn => ?_⟩
    have hn' : n = 16 := congrArg Region.len (Option.some.inj (hn.symm.trans hc.2.2))
    rw [hn']; rfl
  case free bytes hc =>
    refine ⟨hc.2.2.2.1, fun n hn => ?_⟩
    have hn' : n = bytes := congrArg Region.len (Option.some.inj (hn.symm.trans hc.2.2.2.2.2))
    rw [hn']

theorem Exec.sp {c : Prog isa} {s s' : State} {t : List Leak} (h : VG.Exec isa c s t s') :
    s'.sp = s.sp := by
  induction h with
  | block h => exact execBlock_sp h
  | seq _ _ ih₁ ih₂ => exact ih₂.trans ih₁
  | iteT _ _ ih => exact ih
  | iteF _ _ ih => exact ih
  | loopExit _ _ ih => exact ih
  | loopNext _ _ _ ih₁ ih₂ => exact ih₂.trans ih₁
  | call hc _ hr ih =>
    simp only [isa, call, ret, Option.some.injEq] at hc hr
    subst hc; obtain ⟨-, h⟩ := Option.ite_none_right_eq_some.mp hr; cases h; exact ih
  | frame hp _ hq ih =>
    obtain ⟨h₁, h₂⟩ := pop_sp hq
    obtain ⟨n, hn, hs⟩ := push_sp hp
    rw [h₂ n hn, ih, hs, BitVec.sub_add_cancel]

end VG.AArch64

namespace VG.AArch64

/-! Symbolic execution of a block, one instruction at a time (see `runStep`).
These are deliberately not proved by `rfl`: `simp` would use an `rfl` lemma
as a definitional unfolding, which the kernel then re-checks by unfolding the
structural recursion of `runBlock` over the whole remaining block, at every
instruction. -/

theorem runBlock_nil {s : State} : runBlock isa ([] : List Instr) s = some s := by
  rw [runBlock]

theorem runBlock_cons {i : Instr} {is : List Instr} {s : State} :
    runBlock isa (i :: is : List Instr) s = runStep isa (exec i s) is := by
  rw [runBlock]; rfl

theorem runStep_some {s : State} {is : List Instr} :
    runStep isa (some s : Option State) is = runBlock isa is s := by
  rw [runStep]; rfl

end VG.AArch64
