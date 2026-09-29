import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.TCB.AArch64.Isa

/-!
# AArch64: blocks that only move values between registers

Untrusted: everything here is checked by Lean.

As on x86-64 (`Proof/Framework/X86_64/RegBlock.lean`): a block of register
moves, additions and subtractions (of registers or immediates), immediate
loads, shifts and byte reversals (such as the code that sets up the
arguments of a call) runs without faulting, leaves memory, the stack pointer
and the permissions alone, and computes its registers as `run` does from the
registers it starts with. `run` evaluates by unfolding (the block is
concrete), so `wp_run rfl` gives the registers as a chain of `upd`s, which
`simp only [upd]` reads register by register.
-/

namespace VG.AArch64.RegBlock

/-- `g` with `d` set to `v`. -/
def upd (g : Reg → BitVec 64) (d : Reg) (v : BitVec 64) : Reg → BitVec 64 :=
  fun r => if r = d then v else g r

/-- What an instruction does to the registers, if it only reads and writes
registers. -/
def step (g : Reg → BitVec 64) : Instr → Option (Reg → BitVec 64)
  | .addImm .x d n imm => if imm < 4096 then some (upd g d (g n + BitVec.ofNat 64 imm)) else none
  | .subImm .x d n imm => if imm < 4096 then some (upd g d (g n - BitVec.ofNat 64 imm)) else none
  | .addImm .w d n imm =>
    if imm < 4096 then some (upd g d (((g n).setWidth 32 + BitVec.ofNat 32 imm).setWidth 64)) else none
  | .subImm .w d n imm =>
    if imm < 4096 then some (upd g d (((g n).setWidth 32 - BitVec.ofNat 32 imm).setWidth 64)) else none
  | .add .x d n m => some (upd g d (g n + g m))
  | .sub .x d n m => some (upd g d (g n - g m))
  | .movz .x d imm 0 => some (upd g d (imm.setWidth 64))
  | .lsr .x d n sh => if sh < 64 then some (upd g d (g n >>> sh)) else none
  | .rev32 d n => some (upd g d ((rev32 ((g n).setWidth 32)).setWidth 64))
  | _ => none

/-- What a block does to the registers, if it only reads and writes registers. -/
def run (g : Reg → BitVec 64) : List Instr → Option (Reg → BitVec 64)
  | [] => some g
  | i :: is => (step g i).bind fun g' => run g' is

theorem write_gpr (s : State) (sz : Size) (d : Reg) (v : BitVec sz.bits) :
    (s.write sz d v).gpr = upd s.gpr d (v.setWidth 64) := rfl

theorem step_exec {s : State} {i : Instr} {g : Reg → BitVec 64} (h : step s.gpr i = some g) :
    ∃ s', exec i s = some s' ∧ s'.gpr = g ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      s'.sp = s.sp := by
  have fin : ∀ {s' : State}, exec i s = some s' → s'.gpr = g → s'.mem = s.mem → s'.rd = s.rd →
      s'.wr = s.wr → s'.sp = s.sp → ∃ s', exec i s = some s' ∧ s'.gpr = g ∧ s'.mem = s.mem ∧
        s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := fun e a b c d f => ⟨_, e, a, b, c, d, f⟩
  cases i with
  | addImm sz d n imm =>
    by_cases hc : imm < 4096
    · cases sz <;> simp only [step, hc, ite_true, Option.some.injEq] at h <;> subst h <;>
        exact ⟨_, ite_eq_left_of_eq_true _ _ (eq_true hc), by simp [write_gpr, State.read], rfl, rfl, rfl, rfl⟩
    · cases sz <;> simp [step, hc] at h
  | subImm sz d n imm =>
    by_cases hc : imm < 4096
    · cases sz <;> simp only [step, hc, ite_true, Option.some.injEq] at h <;> subst h <;>
        exact ⟨_, ite_eq_left_of_eq_true _ _ (eq_true hc), by simp [write_gpr, State.read], rfl, rfl, rfl, rfl⟩
    · cases sz <;> simp [step, hc] at h
  | add sz d n m =>
    cases sz <;> simp only [step, Option.some.injEq, reduceCtorEq] at h
    subst h; exact fin rfl (by simp [write_gpr, State.read]) rfl rfl rfl rfl
  | sub sz d n m =>
    cases sz <;> simp only [step, Option.some.injEq, reduceCtorEq] at h
    subst h; exact fin rfl (by simp [write_gpr, State.read]) rfl rfl rfl rfl
  | movz sz d imm hw =>
    cases sz <;> cases hw <;> simp only [step, Option.some.injEq, reduceCtorEq] at h
    subst h; exact ⟨s.write .x d (imm.setWidth 64 <<< (16 * 0)), by simp [exec], by simp [write_gpr], rfl, rfl, rfl, rfl⟩
  | lsr sz d n sh =>
    by_cases hc : sh < 64
    · cases sz <;> simp only [step, hc, ite_true, Option.some.injEq, reduceCtorEq] at h
      subst h
      exact ⟨_, ite_eq_left_of_eq_true _ _ (eq_true hc), by simp [write_gpr, State.read], rfl, rfl, rfl, rfl⟩
    · cases sz <;> simp [step, hc] at h
  | rev32 d n =>
    simp only [step, Option.some.injEq] at h
    subst h; exact fin rfl rfl rfl rfl rfl rfl
  | _ => simp [step] at h

/-- A block that only moves values between registers. -/
theorem wp_run {is : List Instr} {s : State} {g : Reg → BitVec 64} (h : run s.gpr is = some g)
    {rest : List Instr} {Q : State → Prop}
    (k : ∀ s', s'.gpr = g → s'.mem = s.mem → s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp →
      WP isa (.block rest) s' Q) :
    WP isa (.block (is ++ rest)) s Q := by
  induction is generalizing s with
  | nil =>
    simp only [run, Option.some.injEq] at h
    exact k s h rfl rfl rfl rfl
  | cons i is ih =>
    simp only [run, Option.bind_eq_some_iff] at h
    obtain ⟨g₁, h₁, h₂⟩ := h
    obtain ⟨s₁, e₁, g₁', m₁, rd₁, wr₁, sp₁⟩ := step_exec h₁
    rw [← g₁'] at h₂
    exact WP.block_cons_iff.mpr ⟨s₁, e₁, ih h₂ fun s' a b c d e =>
      k s' a (b.trans m₁) (c.trans rd₁) (d.trans wr₁) (e.trans sp₁)⟩

/-- `wp_run` for a whole block. -/
theorem wp_run' {is : List Instr} {s : State} {g : Reg → BitVec 64} (h : run s.gpr is = some g)
    {Q : State → Prop}
    (k : ∀ s', s'.gpr = g → s'.mem = s.mem → s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp → Q s') :
    WP isa (.block is) s Q := by
  have := wp_run (rest := []) h fun s' a b c d e => WP.block_nil (k s' a b c d e)
  rwa [List.append_nil] at this

end VG.AArch64.RegBlock
