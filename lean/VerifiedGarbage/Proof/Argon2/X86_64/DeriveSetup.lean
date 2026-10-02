import VerifiedGarbage.Proof.Argon2.X86_64.DeriveEntry
import VerifiedGarbage.Proof.Argon2.X86_64.DeriveStores
import VerifiedGarbage.Proof.Argon2.X86_64.DeriveScratch
import VerifiedGarbage.TCB.X86_64.Target
import VerifiedGarbage.Proof.Framework.X86_64.Inline

/-! Save the register arguments into the local derivation frame. -/

namespace VG.Proof.Argon2.X86_64.Derive

open VG VG.X86_64

def arguments : List (Nat × Reg) :=
  [(72, .r9), (80, .r8), (88, .rcx), (96, .rdx), (104, .rsi), (112, .rdi)]

def argumentValue (s : State) (r : Reg) : Addr :=
  if r = .rdi ∨ r = .r9 then ((s.gpr r).setWidth 32).setWidth 64 else s.gpr r

theorem Entered.argument {s t : State} (h : Entered s t) (r : Reg) (bp : r ≠ .rbp) :
    t.gpr r = argumentValue s r := by
  unfold argumentValue
  by_cases di : r = .rdi
  · subst r; rw [ite_eq_left (Or.inl rfl)]; exact h.kind
  · by_cases nine : r = .r9
    · subst r; rw [ite_eq_left (Or.inr rfl)]; exact h.passes
    · rw [ite_eq_right (by simp only [di, nine, or_self, not_false_eq_true])]
      exact h.regs r bp di nine

structure SetupDone (s t : State) : Prop where
  bp : t.gpr .rbp = s.gpr .rsp
  sp : t.gpr .rsp = s.gpr .rsp
  scratch : t.gpr .rbx = s.mem.readW (s.gpr .rsp + 248) 64
  values : ∀ arg ∈ arguments, t.mem.readW (t.gpr .rbp + BitVec.ofNat 64 arg.1) 64 = argumentValue s arg.2
  regs : ∀ r ∈ calleeSaved, r ≠ .rbp → r ≠ .rbx → t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  mxcsr : t.mxcsr = s.mxcsr
  frame : Frame [⟨s.gpr .rsp, 120⟩] s.mem t.mem

theorem setup_ok (s : State) (frameWrite : Covers [⟨s.gpr .rsp, 120⟩] s.wr)
    (read : InRegions (s.rd ++ s.wr) (s.gpr .rsp + 248) 8) :
    WP isa (.block Impl.Argon2.X86_64.Derive.setup) s (SetupDone s) := by
  change WP isa (.block (([.mov .rbp (.reg .rsp), .mov32 .rdi (.reg .rdi), .mov32 .r9 (.reg .r9)] : List Instr) ++
    (arguments.map fun arg => .store (Impl.Argon2.X86_64.at_ .rbp arg.1) arg.2) ++
    ([.mov .rbx (.mem (Impl.Argon2.X86_64.at_ .rbp 248))] : List Instr))) s _
  rw [List.append_assoc, WP.block_append_iff]
  refine (entry_ok s).mono ?_
  intro a entered
  rw [WP.block_append_iff]
  have write : ∀ arg ∈ arguments, InRegions a.wr (a.gpr .rbp + BitVec.ofNat 64 arg.1) 8 := by
    intro arg ha
    rw [entered.wr, entered.bp]
    apply frameWrite
    have bounds : ∀ arg ∈ arguments, arg.1 + 8 ≤ 120 := by decide
    exact ⟨_, List.mem_singleton_self _, Offset.contains_base _ (bounds arg ha) (by have := bounds arg ha; omega)⟩
  refine (stores_values_ok arguments a write (by decide) (by decide)).mono ?_
  rintro b ⟨saved, values⟩
  have bp : b.gpr .rbp = s.gpr .rsp := by rw [saved.regs, entered.bp]
  have scratchWord : b.mem.readW (b.gpr .rbp + 248) 64 = s.mem.readW (s.gpr .rsp + 248) 64 := by
    have kept := saved.other_word 248 (by decide) (by decide) (by decide)
    change b.mem.readW (b.gpr .rbp + 248) 64 = a.mem.readW (a.gpr .rbp + 248) 64 at kept
    rw [kept, entered.bp, entered.mem]
  refine (scratch_ok b (by rw [saved.rd, saved.wr, bp, entered.rd, entered.wr]; exact read)).mono ?_
  intro t loaded
  refine ⟨(loaded.regs .rbp (by decide)).trans bp, ?_, loaded.scratch.trans scratchWord, ?_, ?_,
    loaded.rd.trans (saved.rd.trans entered.rd), loaded.wr.trans (saved.wr.trans entered.wr),
    loaded.mxcsr.trans (saved.mxcsr.trans entered.mxcsr), ?_⟩
  · rw [loaded.regs .rsp (by decide), saved.regs]
    exact entered.regs .rsp (by decide) (by decide) (by decide)
  · intro arg ha
    rw [loaded.mem, loaded.regs .rbp (by decide), values arg ha]
    have notBp : ∀ arg ∈ arguments, arg.2 ≠ .rbp := by decide
    exact entered.argument arg.2 (notBp arg ha)
  · intro r hr hb hx
    have other : ∀ r ∈ calleeSaved, r ≠ .rdi ∧ r ≠ .r9 := by decide
    rw [loaded.regs r hx, saved.regs]
    exact entered.regs r hb (other r hr).1 (other r hr).2
  · rw [loaded.mem, ← entered.mem]
    have frame := saved.frame
    rw [entered.bp] at frame
    apply frame.sub
    intro region hr
    obtain ⟨arg, ha, rfl⟩ := List.mem_map.mp hr
    have bounds : ∀ arg ∈ arguments, arg.1 + 8 ≤ 120 := by decide
    exact ⟨_, List.mem_singleton_self _, Offset.sub_base _ (bounds arg ha)⟩

end VG.Proof.Argon2.X86_64.Derive
