import VerifiedGarbage.Proof.Argon2.X86_64.DeriveNormalize

/-! Copy a read-only caller argument into the private derivation frame. -/

namespace VG.Proof.Argon2.X86_64.Derive

open VG VG.X86_64

def copySource (j : Nat) : Nat := 328 + 8 * j
def copyDestination (j : Nat) : Nat := 176 + 8 * j

structure CopiedArg (s t : State) (j : Nat) : Prop where
  mem : t.mem = s.mem.writeW (s.gpr .rsp + BitVec.ofNat 64 (copyDestination j))
    (s.mem.readW (s.gpr .rsp + BitVec.ofNat 64 (copySource j)) 64)
  regs : ∀ r, r ≠ .rax → t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  mxcsr : t.mxcsr = s.mxcsr

theorem copyArg_ok (s : State) (j : Nat)
    (read : InRegions (s.rd ++ s.wr) (s.gpr .rsp + BitVec.ofNat 64 (copySource j)) 8)
    (write : InRegions s.wr (s.gpr .rsp + BitVec.ofNat 64 (copyDestination j)) 8) :
    WP isa (.block (Impl.Argon2.X86_64.Derive.copyArg j)) s (CopiedArg s · j) := by
  change InRegions (s.rd ++ s.wr) (s.gpr .rsp + BitVec.ofNat 64 (328 + 8 * j)) 8 at read
  change InRegions s.wr (s.gpr .rsp + BitVec.ofNat 64 (176 + 8 * j)) 8 at write
  apply WP.of_runBlock
  simp only [Impl.Argon2.X86_64.Derive.copyArg, runBlock_cons, runStep_some, runBlock_nil,
    exec, State.load64, State.store64, readSrc, State.ea, Impl.Argon2.X86_64.at_,
    BitVec.ofInt_natCast, RegUpd.gpr_setReg, RegUpd.mem_setReg, RegUpd.rd_setReg,
    RegUpd.wr_setReg, read, write, reduceCtorEq,
    ite_true, ite_false, Option.some.injEq, Option.map_some, exists_eq_left']
  refine ⟨rfl, ?_, rfl, rfl, rfl⟩
  intro r hr
  exact RegUpd.gpr_setReg_of_ne _ _ hr

theorem CopiedArg.frame {s t : State} {j : Nat} (h : CopiedArg s t j) :
    Frame [⟨s.gpr .rsp + BitVec.ofNat 64 (copyDestination j), 8⟩] s.mem t.mem := by
  rw [h.mem]
  exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)

theorem CopiedArg.word {s t : State} {j : Nat} (h : CopiedArg s t j) :
    t.mem.readW (t.gpr .rsp + BitVec.ofNat 64 (copyDestination j)) 64 =
      s.mem.readW (s.gpr .rsp + BitVec.ofNat 64 (copySource j)) 64 := by
  rw [h.regs .rsp (by decide), h.mem, Mem.readW_writeW_self64]

end VG.Proof.Argon2.X86_64.Derive
