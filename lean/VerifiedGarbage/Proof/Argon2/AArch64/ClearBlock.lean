import VerifiedGarbage.Impl.Argon2.AArch64.ClearBlock
import VerifiedGarbage.Proof.Argon2.AArch64.MemoryInitClearMemory
import VerifiedGarbage.Proof.Argon2.AArch64.Initialize
import VerifiedGarbage.Proof.Framework.AArch64.Inline
import VerifiedGarbage.Proof.Argon2.AArch64.AddressHeaderWords

/-! Zero every word, preserving the enclosing loop's registers and memory. -/

namespace VG.Proof.Argon2.AArch64.ClearBlock

open VG VG.AArch64 VG.Spec.Argon2 VG.Impl.Argon2.AArch64.ClearBlock

theorem word_ok (s : State) (i : Nat) (hi : i < 128)
    (hw : InRegions s.wr (off (s.gpr .x0) (8 * i)) 8) :
    WP isa (.block (Impl.Argon2.AArch64.ClearBlock.word i)) s fun t =>
      t.mem = s.mem.writeW (off (s.gpr .x0) (8 * i)) (s.gpr .x8) ∧
      t.gpr = s.gpr ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp :=
  AddressHeader.registerWord_ok s i .x8 hi hw

theorem prefix_ok (n : Nat) (hn : n ≤ 128) (s : State) (zero : s.gpr .x8 = 0)
    (write : Covers [⟨s.gpr .x0, 1024⟩] s.wr) :
    WP isa (.block (words n)) s fun t =>
      t.mem = MemoryInit.clearMem s.mem (s.gpr .x0) n ∧
      t.gpr = s.gpr ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp := by
  induction n with
  | zero => exact WP.block_nil ⟨rfl, rfl, rfl, rfl, rfl⟩
  | succ n ih =>
    simp only [words, List.range_succ, List.flatMap_append, List.flatMap_cons,
      List.flatMap_nil, List.append_nil]
    apply WP.block_append
    refine (ih (by omega)).mono ?_
    rintro a ⟨mem, regs, rd, wr, mx⟩
    have hw : InRegions a.wr (off (a.gpr .x0) (8 * n)) 8 := by
      rw [regs, wr]
      exact write _ _ ⟨⟨s.gpr .x0, 1024⟩, by simp,
        Offset.contains_base _ (d := 8 * n) (n := 8) (k := 1024) (by omega) (by omega)⟩
    refine (word_ok a n (by omega) hw).mono ?_
    rintro t ⟨mem', regs', rd', wr', mx'⟩
    refine ⟨?_, regs'.trans regs, rd'.trans rd, wr'.trans wr, mx'.trans mx⟩
    rw [mem', regs, zero, mem]
    rfl

theorem zero_ok (s : State) :
    WP isa (.block [VG.Impl.Argon2.AArch64.Instructions.imm .x8 0].flatten) s fun t =>
      t.gpr .x8 = 0 ∧ (∀ r, r ≠ .x8 → t.gpr r = s.gpr r) ∧
      t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp := by
  apply WP.of_runBlock
  simp only [VG.Impl.Argon2.AArch64.Instructions.imm,
    show 0 < 65536 from by decide, ite_true, List.flatten_cons, List.flatten_nil,
    List.cons_append, List.nil_append, runBlock_cons, runStep_some, runBlock_nil,
    exec, Size.bits, Nat.reduceMul, Nat.reduceLT, BitVec.shiftLeft_zero,
    RegUpd.gpr_write, Option.some.injEq, exists_eq_left']
  refine ⟨rfl, ?_, rfl, rfl, rfl, rfl⟩
  intro r hr
  exact ite_eq_right hr

theorem code_ok (s : State) (write : Covers [⟨s.gpr .x0, 1024⟩] s.wr) :
    WP isa code s fun t => blockAt t.mem (s.gpr .x0) = zeroBlock ∧
      Frame [⟨s.gpr .x0, 1024⟩] s.mem t.mem ∧ CopyKeeps s t ∧ t.sp = s.sp := by
  unfold code
  refine WP.seq ((zero_ok s).mono ?_)
  rintro a ⟨zero, regs, mem, rd, wr, mx⟩
  have dest : a.gpr .x0 = s.gpr .x0 := regs .x0 (by decide)
  have write' : Covers [⟨a.gpr .x0, 1024⟩] a.wr := by rw [dest, wr]; exact write
  refine (prefix_ok 128 (by decide) a zero write').mono ?_
  rintro t ⟨mem', regs', rd', wr', mx'⟩
  have cleared : t.mem = MemoryInit.clearMem s.mem (s.gpr .x0) 128 := by
    rw [mem', mem, dest]
  refine ⟨?_, ?_, ⟨fun r hr _ => (congrFun regs' r).trans (regs r hr), rd'.trans rd, wr'.trans wr⟩,
    mx'.trans mx⟩
  · rw [cleared]
    apply Vector.ext
    intro i hi
    change (blockAt _ _)[(⟨i, hi⟩ : Fin 128)] = zeroBlock[(⟨i, hi⟩ : Fin 128)]
    rw [blockAt_get, MemoryInit.clearMem_word _ _ 128 i (by decide) hi]
    simp only [zeroBlock, Fin.getElem_fin, Vector.getElem_replicate]
  · rw [cleared]
    exact MemoryInit.clearMem_frame _ _ 128 (by decide)

end VG.Proof.Argon2.AArch64.ClearBlock
