import VerifiedGarbage.Impl.Argon2.AArch64.Derive
import VerifiedGarbage.Proof.Argon2.AArch64.InitialArgs
import VerifiedGarbage.Proof.Framework.Offset

/-! Normalize u32 stack arguments without assuming anything about their upper bits. -/

namespace VG.Proof.Argon2.AArch64.Derive

open VG VG.AArch64
open VG.Impl.Argon2.AArch64.Derive

structure Normalized (s t : State) (d : Nat) : Prop where
  mem : t.mem = s.mem.writeW (s.gpr .x19 + BitVec.ofNat 64 d)
    (((s.mem.readW (s.gpr .x19 + BitVec.ofNat 64 d) 64).setWidth 32).setWidth 64)
  regs : ∀ r, r ≠ .x8 → t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp

theorem normalize_ok (s : State) (d : Nat)
    (aligned : d % 8 = 0) (bound : d < 32768)
    (read : InRegions (s.rd ++ s.wr) (s.gpr .x19 + BitVec.ofNat 64 d) 8)
    (write : InRegions s.wr (s.gpr .x19 + BitVec.ofNat 64 d) 8) :
    WP isa (.block (normalize d)) s (Normalized s · d) := by
  apply WP.of_runBlock
  simp only [normalize, Impl.Argon2.AArch64.Instructions.load,
    Impl.Argon2.AArch64.Instructions.mov32, Impl.Argon2.AArch64.Instructions.store,
    List.cons_append, List.nil_append, runBlock_cons, runStep_some, runBlock_nil,
    exec, State.read, State.load, State.store, addr, Size.bytes, Size.bits,
    aligned, bound, and_self, RegUpd.gpr_write, RegUpd.mem_write,
    RegUpd.rd_write, RegUpd.wr_write, read, write, BitVec.setWidth_eq,
    BitVec.or_self, reduceCtorEq, ite_true, ite_false, Option.map_some,
    Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨rfl, ?_, rfl, rfl, rfl⟩
  intro r hr
  simp only [RegUpd.gpr_write, hr, ite_false]

theorem Normalized.word {s t : State} {d : Nat} (h : Normalized s t d) :
    t.mem.readW (t.gpr .x19 + BitVec.ofNat 64 d) 64 =
      (((s.mem.readW (s.gpr .x19 + BitVec.ofNat 64 d) 64).setWidth 32).setWidth 64) := by
  rw [h.regs .x19 (by decide), h.mem, Mem.readW_writeW_self64]

theorem Normalized.frame {s t : State} {d : Nat} (h : Normalized s t d) :
    Frame [⟨s.gpr .x19 + BitVec.ofNat 64 d, 8⟩] s.mem t.mem := by
  rw [h.mem]
  exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)

theorem Normalized.other_word {s t : State} {d : Nat} (h : Normalized s t d)
    (e : Nat) (separate : e + 8 ≤ d ∨ d + 8 ≤ e) (ed : e + 8 < 2 ^ 64) (dd : d + 8 < 2 ^ 64) :
    t.mem.readW (t.gpr .x19 + BitVec.ofNat 64 e) 64 = s.mem.readW (s.gpr .x19 + BitVec.ofNat 64 e) 64 := by
  rw [h.regs .x19 (by decide), h.mem]
  exact Mem.readW_writeW_sep (Offset.sep _ separate (Nat.le_of_lt ed) (Nat.le_of_lt dd)) (by decide)

end VG.Proof.Argon2.AArch64.Derive
