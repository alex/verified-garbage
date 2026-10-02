import VerifiedGarbage.Impl.Argon2.X86_64.ClearBlock
import VerifiedGarbage.Proof.Argon2.X86_64.MemoryInitClear
import VerifiedGarbage.Proof.Argon2.X86_64.Initialize
import VerifiedGarbage.Proof.Framework.X86_64.Inline

/-! Zero every word, preserving the enclosing loop's registers and memory. -/

namespace VG.Proof.Argon2.X86_64.ClearBlock

open VG VG.X86_64 VG.Spec.Argon2 VG.Impl.Argon2.X86_64.ClearBlock

theorem word_ok (s : State) (i : Nat)
    (hw : InRegions s.wr (off (s.gpr .rdi) (8 * i)) 8) :
    WP isa (.block (Impl.Argon2.X86_64.ClearBlock.word i)) s fun t =>
      t.mem = s.mem.writeW (off (s.gpr .rdi) (8 * i)) (s.gpr .rax) ∧
      t.gpr = s.gpr ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.mxcsr = s.mxcsr := by
  apply WP.of_runBlock
  simp only [Impl.Argon2.X86_64.ClearBlock.word, runBlock_cons, runStep_some, runBlock_nil,
    exec, State.store64, ea_at, hw, ite_true, Option.some.injEq, exists_eq_left']
  exact ⟨trivial, trivial, trivial, trivial, trivial⟩

theorem prefix_ok (n : Nat) (hn : n ≤ 128) (s : State) (zero : s.gpr .rax = 0)
    (write : Covers [⟨s.gpr .rdi, 1024⟩] s.wr) :
    WP isa (.block (words n)) s fun t =>
      t.mem = MemoryInit.clearMem s.mem (s.gpr .rdi) n ∧
      t.gpr = s.gpr ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.mxcsr = s.mxcsr := by
  induction n with
  | zero => exact WP.block_nil ⟨rfl, rfl, rfl, rfl, rfl⟩
  | succ n ih =>
    simp only [words, List.range_succ, List.flatMap_append, List.flatMap_cons,
      List.flatMap_nil, List.append_nil]
    apply WP.block_append
    refine (ih (by omega)).mono ?_
    rintro a ⟨mem, regs, rd, wr, mx⟩
    have hw : InRegions a.wr (off (a.gpr .rdi) (8 * n)) 8 := by
      rw [regs, wr]
      exact write _ _ ⟨⟨s.gpr .rdi, 1024⟩, by simp,
        Offset.contains_base _ (d := 8 * n) (n := 8) (k := 1024) (by omega) (by omega)⟩
    refine (word_ok a n hw).mono ?_
    rintro t ⟨mem', regs', rd', wr', mx'⟩
    refine ⟨?_, regs'.trans regs, rd'.trans rd, wr'.trans wr, mx'.trans mx⟩
    rw [mem', regs, zero, mem]
    rfl

theorem zero_ok (s : State) : WP isa (.block [.mov .rax (.imm 0)]) s fun t =>
    t.gpr .rax = 0 ∧ (∀ r, r ≠ .rax → t.gpr r = s.gpr r) ∧
    t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.mxcsr = s.mxcsr := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc,
    Option.map_some, Option.some.injEq, exists_eq_left', RegUpd.gpr_setReg, ite_true]
  refine ⟨rfl, ?_, rfl, rfl, rfl, rfl⟩
  intro r hr
  exact ite_eq_right hr

theorem code_ok (s : State) (write : Covers [⟨s.gpr .rdi, 1024⟩] s.wr) :
    WP isa code s fun t => blockAt t.mem (s.gpr .rdi) = zeroBlock ∧
      Frame [⟨s.gpr .rdi, 1024⟩] s.mem t.mem ∧ CopyKeeps s t ∧ t.mxcsr = s.mxcsr := by
  unfold code
  refine WP.seq ((zero_ok s).mono ?_)
  rintro a ⟨zero, regs, mem, rd, wr, mx⟩
  have dest : a.gpr .rdi = s.gpr .rdi := regs .rdi (by decide)
  have write' : Covers [⟨a.gpr .rdi, 1024⟩] a.wr := by rw [dest, wr]; exact write
  refine (prefix_ok 128 (by decide) a zero write').mono ?_
  rintro t ⟨mem', regs', rd', wr', mx'⟩
  have cleared : t.mem = MemoryInit.clearMem s.mem (s.gpr .rdi) 128 := by
    rw [mem', mem, dest]
  refine ⟨?_, ?_, ⟨fun r hr => (congrFun regs' r).trans (regs r hr), rd'.trans rd, wr'.trans wr⟩,
    mx'.trans mx⟩
  · rw [cleared]
    apply Vector.ext
    intro i hi
    change (blockAt _ _)[(⟨i, hi⟩ : Fin 128)] = zeroBlock[(⟨i, hi⟩ : Fin 128)]
    rw [blockAt_get, MemoryInit.clearMem_word _ _ 128 i (by decide) hi]
    simp only [zeroBlock, Fin.getElem_fin, Vector.getElem_replicate]
  · rw [cleared]
    exact MemoryInit.clearMem_frame _ _ 128 (by decide)

end VG.Proof.Argon2.X86_64.ClearBlock
