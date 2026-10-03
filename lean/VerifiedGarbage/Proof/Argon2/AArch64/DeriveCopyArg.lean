import VerifiedGarbage.Proof.Argon2.AArch64.DeriveNormalize

/-! Copy a read-only caller argument into the private derivation frame. -/

namespace VG.Proof.Argon2.AArch64.Derive

open VG VG.AArch64

def copySource (j : Nat) : Nat := 384 + 8 * j
def copyDestination (j : Nat) : Nat := 192 + 8 * j

structure CopiedArg (s t : State) (j : Nat) : Prop where
  mem : t.mem = s.mem.writeW (s.sp + BitVec.ofNat 64 (copyDestination j))
    (s.mem.readW (s.sp + BitVec.ofNat 64 (copySource j)) 64)
  regs : ∀ r, r ≠ .x8 → t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp

theorem copyArg_ok (s : State) (j : Nat)
    (bound : j < 10) (bp : s.gpr .x19 = s.sp)
    (read : InRegions (s.rd ++ s.wr) (s.sp + BitVec.ofNat 64 (copySource j)) 8)
    (write : InRegions s.wr (s.sp + BitVec.ofNat 64 (copyDestination j)) 8) :
    WP isa (.block (Impl.Argon2.AArch64.Derive.copyArg j)) s (CopiedArg s · j) := by
  have sourceAlign : copySource j % 8 = 0 := by unfold copySource; omega
  have sourceBound : copySource j < 32768 := by unfold copySource; omega
  have destAlign : copyDestination j % 8 = 0 := by unfold copyDestination; omega
  have destBound : copyDestination j < 32768 := by unfold copyDestination; omega
  apply WP.of_runBlock
  simp only [Impl.Argon2.AArch64.Derive.copyArg,
    show 384 + 8 * j = copySource j from rfl,
    show 192 + 8 * j = copyDestination j from rfl,
    runBlock_cons, runStep_some, runBlock_nil, exec, State.read, State.load,
    State.store, addr, Size.bytes, Size.bits,
    sourceAlign, sourceBound, destAlign, destBound, and_self,
    RegUpd.gpr_write, RegUpd.mem_write, RegUpd.rd_write, RegUpd.wr_write,
    bp, read, write, BitVec.setWidth_eq, reduceCtorEq, ite_true, ite_false,
    Option.map_some, Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨rfl, ?_, rfl, rfl, rfl⟩
  intro r hr
  simp only [RegUpd.gpr_write, hr, ite_false]

theorem CopiedArg.frame {s t : State} {j : Nat} (h : CopiedArg s t j) :
    Frame [⟨s.sp + BitVec.ofNat 64 (copyDestination j), 8⟩] s.mem t.mem := by
  rw [h.mem]
  exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)

theorem CopiedArg.word {s t : State} {j : Nat} (h : CopiedArg s t j) :
    t.mem.readW (t.sp + BitVec.ofNat 64 (copyDestination j)) 64 =
      s.mem.readW (s.sp + BitVec.ofNat 64 (copySource j)) 64 := by
  rw [h.sp, h.mem, Mem.readW_writeW_self64]

end VG.Proof.Argon2.AArch64.Derive
