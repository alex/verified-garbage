import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum.Basic
import Mathlib.Tactic.Ring.Basic
import Mathlib.Tactic.Tauto
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.Set
import Mathlib.Tactic.Use
import Mathlib.Tactic.ByContra
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.X86_64.Bswap
import VerifiedGarbage.TCB.AArch64.Isa
import VerifiedGarbage.Proof.Framework.Block

/-!
# AArch64: instruction-level rewrite lemmas for symbolic execution

Untrusted: everything here is checked by Lean.
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

/-- `movz` of the low half then `movk` of the high half builds the word. -/
theorem movz_movk (x : BitVec 32) :
    (x.extractLsb' 0 16).setWidth 32 &&& 0xFFFF ||| (x.extractLsb' 16 16).setWidth 32 <<< 16 = x := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  interval_cases i <;> simp

theorem exec_add {sz : Size} {s : State} {d n m : Reg} :
    exec (.add sz d n m) s = some (s.write sz d (s.read sz n + s.read sz m)) := rfl

theorem exec_logic {op : LogicOp} {sz : Size} {s : State} {d n m : Reg} :
    exec (.logic op sz d n m) s = some (s.write sz d (match op with
      | .and => s.read sz n &&& s.read sz m | .orr => s.read sz n ||| s.read sz m
      | .eor => s.read sz n ^^^ s.read sz m)) := rfl

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
  interval_cases i <;> simp

theorem rev32_readW (m : Mem) (a : Addr) :
    rev32 (m.readW a 32) = (m a ++ m (a + 1) ++ m (a + 1 + 1) ++ m (a + 1 + 1 + 1) : BitVec 32) :=
  X86_64.bswap32_readW m a

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
  interval_cases i <;> simp

/-- A 64-bit load followed by `rev` reads the eight bytes big-endian. -/
theorem rev64_readW (m : Mem) (a : Addr) :
    rev64 (m.readW a 64) = (m a ++ m (a + 1) ++ m (a + 1 + 1) ++ m (a + 1 + 1 + 1) ++
      m (a + 1 + 1 + 1 + 1) ++ m (a + 1 + 1 + 1 + 1 + 1) ++ m (a + 1 + 1 + 1 + 1 + 1 + 1) ++
      m (a + 1 + 1 + 1 + 1 + 1 + 1 + 1) : BitVec 64) :=
  X86_64.bswap64_readW m a

end VG.AArch64

namespace VG.AArch64

theorem exec_sp {i : Instr} {s s' : State} (h : exec i s = some s') : s'.sp = s.sp := by
  cases i <;>
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

/-- No modelled instruction changes `sp`. -/
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
    subst hc; split at hr <;> cases hr; exact ih

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
