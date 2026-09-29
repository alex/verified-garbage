import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.TCB.X86_64.Isa

/-!
# x86-64: blocks that only move values between registers

Untrusted: everything here is checked by Lean.

A block of register-to-register `mov`s, `add`s and `sub`s, immediate loads
and `bswap`s (such as the code that sets up the arguments of a call) runs
without faulting, leaves memory and the permissions alone, and computes its
registers as `run` does from the registers it starts with. `run` evaluates
by unfolding (the block is concrete), so `wp_run rfl` gives the registers
as a chain of `upd`s, which `simp only [upd]` reads register by register.
-/

namespace VG.X86_64.RegBlock

/-- `g` with `d` set to `v`. -/
def upd (g : Reg → BitVec 64) (d : Reg) (v : BitVec 64) : Reg → BitVec 64 :=
  fun r => if r = d then v else g r

/-- What an instruction does to the registers, if it only reads and writes
registers (the flags aside). -/
def step (g : Reg → BitVec 64) : Instr → Option (Reg → BitVec 64)
  | .mov d (.reg r) => some (upd g d (g r))
  | .mov32 d (.reg r) => some (upd g d (((g r).setWidth 32).setWidth 64))
  | .mov32 d (.imm v) => some (upd g d (v.setWidth 64))
  | .alu .add d (.imm v) => some (upd g d (g d + v.signExtend 64))
  | .alu .sub d (.imm v) => some (upd g d (g d - v.signExtend 64))
  | .alu .add d (.reg r) => some (upd g d (g d + g r))
  | .alu .sub d (.reg r) => some (upd g d (g d - g r))
  | .bswap32 d => some (upd g d ((bswap32 ((g d).setWidth 32)).setWidth 64))
  | _ => none

/-- What a block does to the registers, if it only reads and writes registers. -/
def run (g : Reg → BitVec 64) : List Instr → Option (Reg → BitVec 64)
  | [] => some g
  | i :: is => (step g i).bind fun g' => run g' is

theorem step_exec {s : State} {i : Instr} {g : Reg → BitVec 64} (h : step s.gpr i = some g) :
    ∃ s', exec i s = some s' ∧ s'.gpr = g ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  unfold step at h
  split at h <;> first
    | (simp only [Option.some.injEq] at h; subst h; exact ⟨_, rfl, rfl, rfl, rfl, rfl⟩)
    | cases h

/-- A block that only moves values between registers. -/
theorem wp_run {is : List Instr} {s : State} {g : Reg → BitVec 64} (h : run s.gpr is = some g)
    {rest : List Instr} {Q : State → Prop}
    (k : ∀ s', s'.gpr = g → s'.mem = s.mem → s'.rd = s.rd → s'.wr = s.wr → WP isa (.block rest) s' Q) :
    WP isa (.block (is ++ rest)) s Q := by
  induction is generalizing s with
  | nil =>
    simp only [run, Option.some.injEq] at h
    exact k s h rfl rfl rfl
  | cons i is ih =>
    simp only [run, Option.bind_eq_some_iff] at h
    obtain ⟨g₁, h₁, h₂⟩ := h
    obtain ⟨s₁, e₁, g₁', m₁, rd₁, wr₁⟩ := step_exec h₁
    rw [← g₁'] at h₂
    exact WP.block_cons_iff.mpr ⟨s₁, e₁, ih h₂ fun s' a b c d => k s' a (b.trans m₁) (c.trans rd₁) (d.trans wr₁)⟩

/-- `wp_run` for a whole block. -/
theorem wp_run' {is : List Instr} {s : State} {g : Reg → BitVec 64} (h : run s.gpr is = some g)
    {Q : State → Prop} (k : ∀ s', s'.gpr = g → s'.mem = s.mem → s'.rd = s.rd → s'.wr = s.wr → Q s') :
    WP isa (.block is) s Q := by
  have := wp_run (rest := []) h fun s' a b c d => WP.block_nil (k s' a b c d)
  rwa [List.append_nil] at this

end VG.X86_64.RegBlock
