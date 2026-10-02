import VerifiedGarbage.Impl.Argon2.X86_64.Derive
import VerifiedGarbage.Proof.Argon2.X86_64.InitialArgs
import VerifiedGarbage.Proof.Framework.Offset

/-! Normalize u32 stack arguments without assuming anything about their upper bits. -/

namespace VG.Proof.Argon2.X86_64.Derive

open VG VG.X86_64
open VG.Impl.Argon2.X86_64.Derive

structure Normalized (s t : State) (d : Nat) : Prop where
  mem : t.mem = s.mem.writeW (s.gpr .rbp + BitVec.ofNat 64 d)
    (((s.mem.readW (s.gpr .rbp + BitVec.ofNat 64 d) 64).setWidth 32).setWidth 64)
  regs : ∀ r, r ≠ .rax → t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  mxcsr : t.mxcsr = s.mxcsr

theorem normalize_ok (s : State) (d : Nat)
    (read : InRegions (s.rd ++ s.wr) (s.gpr .rbp + BitVec.ofNat 64 d) 8)
    (write : InRegions s.wr (s.gpr .rbp + BitVec.ofNat 64 d) 8) :
    WP isa (.block (normalize d)) s (Normalized s · d) := by
  apply WP.of_runBlock
  simp only [normalize, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc,
    readSrc32, State.load64, State.store64, State.setReg32, State.ea, Impl.Argon2.X86_64.at_, BitVec.ofInt_natCast,
    RegUpd.gpr_setReg, RegUpd.mem_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg,
    read, write, reduceCtorEq, ite_true, ite_false, Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨rfl, ?_, rfl, rfl, rfl⟩
  intro r hr
  simp only [RegUpd.gpr_setReg, hr, ite_false]

theorem Normalized.word {s t : State} {d : Nat} (h : Normalized s t d) :
    t.mem.readW (t.gpr .rbp + BitVec.ofNat 64 d) 64 =
      (((s.mem.readW (s.gpr .rbp + BitVec.ofNat 64 d) 64).setWidth 32).setWidth 64) := by
  rw [h.regs .rbp (by decide), h.mem, Mem.readW_writeW_self64]

theorem Normalized.frame {s t : State} {d : Nat} (h : Normalized s t d) :
    Frame [⟨s.gpr .rbp + BitVec.ofNat 64 d, 8⟩] s.mem t.mem := by
  rw [h.mem]
  exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)

theorem Normalized.other_word {s t : State} {d : Nat} (h : Normalized s t d)
    (e : Nat) (separate : e + 8 ≤ d ∨ d + 8 ≤ e) (ed : e + 8 < 2 ^ 64) (dd : d + 8 < 2 ^ 64) :
    t.mem.readW (t.gpr .rbp + BitVec.ofNat 64 e) 64 = s.mem.readW (s.gpr .rbp + BitVec.ofNat 64 e) 64 := by
  rw [h.regs .rbp (by decide), h.mem]
  exact Mem.readW_writeW_sep (Offset.sep _ separate (Nat.le_of_lt ed) (Nat.le_of_lt dd)) (by decide)

end VG.Proof.Argon2.X86_64.Derive
