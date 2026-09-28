import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum.Basic
import Mathlib.Tactic.Ring.Basic
import Mathlib.Tactic.Tauto
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.Set
import Mathlib.Tactic.Use
import Mathlib.Tactic.ByContra
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.X86_64.Bswap
import VerifiedGarbage.TCB.Arm.Isa

/-!
# ARMv7: instruction-level rewrite lemmas for symbolic execution

Untrusted: everything here is checked by Lean.
-/

namespace VG.Arm

theorem exec_ldr {s : State} {t n : Reg} {off : Nat} (ho : off < 4096)
    (h : InRegions (s.rd ++ s.wr) (State.addr (s.gpr n + BitVec.ofNat 32 off)) 4) :
    exec (.ldr t n off) s =
      some (s.setReg t (s.mem.readW (State.addr (s.gpr n + BitVec.ofNat 32 off)) 32)) := by
  simp only [exec, ho, ite_true, State.load32, h, Option.map_some]

theorem exec_str {s : State} {t n : Reg} {off : Nat} (ho : off < 4096)
    (h : InRegions s.wr (State.addr (s.gpr n + BitVec.ofNat 32 off)) 4) :
    exec (.str t n off) s =
      some { s with mem := s.mem.writeW (State.addr (s.gpr n + BitVec.ofNat 32 off)) (s.gpr t) } := by
  simp only [exec, ho, ite_true, State.store32, h]

/-- `movw` of the low half then `movt` of the high half builds the word. -/
theorem movw_movt (x : BitVec 32) :
    ((x.extractLsb' 16 16 ++ ((x.extractLsb' 0 16).setWidth 32).extractLsb' 0 16 : BitVec 32)) = x := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have e : ∀ a b : BitVec 16, (a ++ b : BitVec (16 + 16)).getLsbD i =
      if i < 16 then b.getLsbD i else a.getLsbD (i - 16) := fun a b => BitVec.getLsbD_append
  rw [e]
  interval_cases i <;> simp

theorem rev_readW (m : Mem) (a : Addr) :
    rev (m.readW a 32) = (m a ++ m (a + 1) ++ m (a + 1 + 1) ++ m (a + 1 + 1 + 1) : BitVec 32) :=
  X86_64.bswap32_readW m a

theorem exec_sp {i : Instr} {s s' : State} (h : exec i s = some s') : s'.sp = s.sp := by
  cases i <;>
  simp only [exec, Option.map_eq_some_iff, State.setReg, State.load32, State.store32, State.load8,
    State.store8, subFlags] at h <;>
  (repeat' split at h) <;>
  (try simp only [Option.some.injEq, reduceCtorEq] at h) <;>
  first
  | (subst h; rfl)
  | (obtain ⟨_, _, rfl⟩ := h; rfl)
  | (cases h)

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

theorem push_sp {i : Instr} {s s₁ : State} (h : push i s = some s₁) :
    ∃ n, s₁.sp = s.sp - BitVec.ofNat 32 n ∧ s₁.wr.head? = some ⟨State.addr s₁.sp, n⟩ := by
  cases i <;> simp only [push, reduceCtorEq] at h
  split at h <;> cases h; exact ⟨_, rfl, rfl⟩

theorem pop_sp {j : Instr} {s₁ s₂ s' : State} (h : pop j s₁ s₂ = some s') :
    s₂.sp = s₁.sp ∧ ∃ n, s₁.wr.head? = some ⟨State.addr s₁.sp, n⟩ ∧
      s'.sp = s₂.sp + BitVec.ofNat 32 n := by
  cases j <;> simp only [pop, reduceCtorEq] at h
  split at h <;> cases h
  rename_i hc; exact ⟨hc.2.2.1, _, hc.2.2.2.2, rfl⟩

/-- `sp` is back where it was after any code: only frames change it. -/
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
  | frame hp _ hq ih =>
    obtain ⟨n, h₁, h₂⟩ := push_sp hp
    obtain ⟨h₃, m, h₄, h₅⟩ := pop_sp hq
    rw [h₂] at h₄; cases h₄
    rw [h₅, ih, h₁, BitVec.sub_add_cancel]

/-- Addresses do not wrap. -/
theorem addr_add {a : BitVec 32} {k : Nat} (h : a.toNat + k < 2 ^ 32) :
    State.addr (a + BitVec.ofNat 32 k) = State.addr a + BitVec.ofNat 64 k := by
  simp only [State.addr]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_add, BitVec.toNat_ofNat]
  have := a.isLt
  rw [Nat.mod_eq_of_lt (a := k) (by omega), Nat.mod_eq_of_lt (a := a.toNat + k) h,
    Nat.mod_eq_of_lt (a := k) (by omega), Nat.mod_eq_of_lt (a := a.toNat) (by omega),
    Nat.mod_eq_of_lt (a := a.toNat + k) (by omega)]

end VG.Arm

namespace VG.Arm

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

end VG.Arm
