import VerifiedGarbage.Proof.Argon2.AArch64.Finish
import VerifiedGarbage.Impl.Argon2.AArch64.FillWrite
import VerifiedGarbage.Proof.Argon2.AArch64.Memory
import VerifiedGarbage.Proof.Argon2.AArch64.DivideStep

/-! Merged from `Proof.Argon2.AArch64.FillWriteWord`. -/
section
/-! One output word, keeping register writes folded during execution. -/

namespace VG.Proof.Argon2.AArch64.FillWrite

open VG VG.AArch64 VG.Impl.Argon2.AArch64.FillWrite
open VG.Impl.Argon2.AArch64

/-- Registers preserved while copying/XORing matrix words and testing the pass. -/
def CopyKeeps (s t : State) : Prop :=
  (∀ r, r ≠ .x8 → r ≠ .x13 → r ≠ .x14 → r ≠ .x15 → t.gpr r = s.gpr r) ∧
    t.rd = s.rd ∧ t.wr = s.wr

theorem CopyKeeps.refl (s : State) : CopyKeeps s s := ⟨fun _ _ _ _ _ => rfl, rfl, rfl⟩
theorem CopyKeeps.trans {s t u : State} (h : CopyKeeps s t) (k : CopyKeeps t u) : CopyKeeps s u :=
  ⟨fun r h8 h13 h14 h15 => (k.1 r h8 h13 h14 h15).trans (h.1 r h8 h13 h14 h15),
    k.2.1.trans h.2.1, k.2.2.trans h.2.2⟩

def value (xorOld : Bool) (m : Mem) (src dest : Addr) (i : Nat) : Addr :=
  let next := m.readW (off src (8 * i)) 64
  if xorOld then next ^^^ m.readW (off dest (8 * i)) 64 else next

/-- The source is readable and the destination writable; its old contents
are read only on later passes. -/
theorem word_ok (xorOld : Bool) (s : State) (i : Nat) (hi : i < 128)
    (hr : InRegions (s.rd ++ s.wr) (off (s.gpr .x1) (8 * i)) 8)
    (hw : InRegions s.wr (off (s.gpr .x0) (8 * i)) 8)
    (ho : InRegions (s.rd ++ s.wr) (off (s.gpr .x0) (8 * i)) 8) :
    WP isa (.block (Impl.Argon2.AArch64.FillWrite.word xorOld i)) s fun t =>
      t.mem = s.mem.writeW (off (s.gpr .x0) (8 * i))
        (value xorOld s.mem (s.gpr .x1) (s.gpr .x0) i) ∧
      (∀ r, r ≠ .x8 → r ≠ .x13 → r ≠ .x14 → r ≠ .x15 → t.gpr r = s.gpr r) ∧
      t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp := by
  have hoff : (8 * i) % 8 = 0 ∧ 8 * i < 4096 * 8 := by omega
  cases xorOld <;> apply WP.of_runBlock <;>
    simp only [Impl.Argon2.AArch64.FillWrite.word, value, Bool.false_eq_true, ite_false, ite_true,
      Instructions.load, Instructions.store, Instructions.xorm, Instructions.logic,
      Instructions.mark, Instructions.mov,
      List.flatten_cons, List.flatten_nil, List.cons_append, List.nil_append,
      runBlock_cons, runStep_some, runBlock_nil, exec, addr, hoff,
      State.load, State.store, State.read, Size.bits, Size.bytes,
      off, hr, hw, ho, and_self, show 0 < 4096 from by decide,
      RegUpd.gpr_write, RegUpd.mem_write, RegUpd.rd_write, RegUpd.wr_write,
      BitVec.setWidth_eq, BitVec.add_zero, reduceCtorEq, ite_true, ite_false,
      Option.map_some, Option.bind_some, Option.some.injEq, exists_eq_left']
  all_goals
    refine ⟨?_, ?_, trivial, trivial, rfl⟩
    · rfl
    · intro r h8 h13 _h14 h15
      simp only [h8, h13, h15, ite_false]

end VG.Proof.Argon2.AArch64.FillWrite
end

/-! Compose the word writes without re-executing a long load/store block. -/

namespace VG.Proof.Argon2.AArch64.FillWrite

open VG VG.AArch64 VG.Spec.Argon2 VG.Impl.Argon2.AArch64.FillWrite

def result (xorOld : Bool) (m : Mem) (src dest : Addr) : Block :=
  if xorOld then xorBlock (blockAt m src) (blockAt m dest) else blockAt m src

theorem result_get (xorOld : Bool) (m : Mem) (src dest : Addr) (i : Fin 128) :
    (result xorOld m src dest)[i] = value xorOld m src dest i.val := by
  cases xorOld <;> simp only [result, value, Bool.false_eq_true, ite_false, ite_true,
    xorBlock_get, blockAt_get]

theorem frame_extend {m m' : Mem} {dest : Addr} {n k : Nat}
    (hf : Frame [⟨dest, 8 * n⟩] m m') (h : n ≤ k) : Frame [⟨dest, 8 * k⟩] m m' := by
  apply hf.sub
  intro r hr
  simp only [List.mem_singleton] at hr
  subst r
  exact ⟨_, by simp, Region.sub_prefix (Nat.mul_le_mul_left 8 h)⟩

theorem source_read {m m' : Mem} {src dest : Addr} {n : Nat}
    (hf : Frame [⟨dest, 8 * n⟩] m m') (hn : n ≤ 128)
    (hd : (⟨src, 1024⟩ : Region).Disjoint ⟨dest, 1024⟩) (i : Fin 128) :
    m'.readW (off src (8 * i.val)) 64 = m.readW (off src (8 * i.val)) 64 := by
  have full := frame_extend hf hn
  exact full.readW (r := ⟨src, 1024⟩)
    (Offset.contains_base src (by omega) (by omega))
    (by intro r hr; simp only [List.mem_singleton] at hr; subst r; exact hd) (by decide)

theorem old_read {m m' : Mem} {dest : Addr} {n : Nat}
    (hf : Frame [⟨dest, 8 * n⟩] m m') (hn : n < 128) :
    m'.readW (off dest (8 * n)) 64 = m.readW (off dest (8 * n)) 64 :=
  hf.readW (r := ⟨off dest (8 * n), 8⟩) (Region.contains_self _ _)
    (by
      intro r hr
      simp only [List.mem_singleton] at hr
      subst r
      exact Offset.disjoint_base dest (Nat.le_refl _) (by omega)) (by decide)

theorem prefix_ok (xorOld : Bool) (n : Nat) (hn : n ≤ 128) (s : State)
    (hs : (⟨s.gpr .x1, 1024⟩ : Region) ∈ s.rd ++ s.wr)
    (hw : (⟨s.gpr .x0, 1024⟩ : Region) ∈ s.wr)
    (hd : (⟨s.gpr .x1, 1024⟩ : Region).Disjoint ⟨s.gpr .x0, 1024⟩) :
    WP isa (.block (words xorOld n)) s fun t =>
      Written t.mem (s.gpr .x0) (result xorOld s.mem (s.gpr .x1) (s.gpr .x0)) n ∧
      Frame [⟨s.gpr .x0, 8 * n⟩] s.mem t.mem ∧ CopyKeeps s t ∧ t.sp = s.sp := by
  induction n with
  | zero => exact WP.block_nil ⟨fun i hi => by omega, Frame.refl _ _, CopyKeeps.refl s, rfl⟩
  | succ n ih =>
    simp only [words, List.range_succ, List.flatMap_append, List.flatMap_cons,
      List.flatMap_nil, List.append_nil]
    apply WP.block_append
    refine (ih (by omega)).mono ?_
    rintro t ⟨written, frame, keeps, mx⟩
    have hn' : n < 128 := by omega
    have src : t.gpr .x1 = s.gpr .x1 := keeps.1 .x1 (by decide) (by decide) (by decide) (by decide)
    have dest : t.gpr .x0 = s.gpr .x0 := keeps.1 .x0 (by decide) (by decide) (by decide) (by decide)
    have write : InRegions t.wr (off (t.gpr .x0) (8 * n)) 8 := by
      rw [dest, keeps.2.2]
      exact ⟨_, hw, Offset.contains_base _ (by omega) (by omega)⟩
    have read : InRegions (t.rd ++ t.wr) (off (t.gpr .x1) (8 * n)) 8 := by
      rw [src, keeps.2.1, keeps.2.2]
      exact ⟨_, hs, Offset.contains_base _ (by omega) (by omega)⟩
    have old : InRegions (t.rd ++ t.wr) (off (t.gpr .x0) (8 * n)) 8 := by
      obtain ⟨r, hr, hc⟩ := write
      exact ⟨r, List.mem_append_right _ hr, hc⟩
    refine (word_ok xorOld t n hn' read write old).mono ?_
    rintro u ⟨mem, regs, rd, wr, mx'⟩
    have v : value xorOld t.mem (t.gpr .x1) (t.gpr .x0) n =
        (result xorOld s.mem (s.gpr .x1) (s.gpr .x0))[(⟨n, hn'⟩ : Fin 128)] := by
      rw [result_get, src, dest]
      unfold value
      rw [source_read frame (by omega) hd ⟨n, hn'⟩]
      cases xorOld
      · rfl
      · rw [old_read frame hn']
    refine ⟨?_, ?_, keeps.trans ⟨regs, rd, wr⟩, mx'.trans mx⟩
    · rw [mem, v, dest]
      exact written_step hn' written
    · rw [mem, dest]
      exact (frame_extend frame (Nat.le_succ n)).writeW
        (r := ⟨s.gpr .x0, 8 * (n + 1)⟩) (by simp) _
        (Offset.contains_base _ (by omega) (by omega))

end VG.Proof.Argon2.AArch64.FillWrite
