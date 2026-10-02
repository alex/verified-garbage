import VerifiedGarbage.Impl.Argon2.AArch64.FillWrite
import VerifiedGarbage.Proof.Argon2.AArch64.Memory
import VerifiedGarbage.Proof.Argon2.AArch64.DivideStep

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
