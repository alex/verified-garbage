import VerifiedGarbage.Proof.TripleDes.X86.FinalPermutation

namespace VG.Proof.TripleDes.X86
open VG VG.X86 VG.X86.RegUpd VG.X86.Straight VG.Impl.TripleDes.X86
open VG.Proof.Rc2.X86 (addr32)

def finalWord (s : State) : BitVec 64 :=
  s.mem.readW (addr (s.gpr .eax) 28) 32 ++ s.mem.readW (addr (s.gpr .eax) 24) 32

theorem restoredOutput_ok (s : State) (fit : (dataArg s).toNat + 8 ≤ 2 ^ 32)
    (harg : InRegions (s.rd ++ s.wr) (wordAddr (s.gpr .esp) 2) 4)
    (hr : ∀ k ∈ [24, 28], InRegions (s.rd ++ s.wr) (addr (s.gpr .eax) k) 4)
    (hw : ∀ i < 2, InRegions s.wr (wordAddr (dataArg s) i) 4) :
    ∃ s', runBlock isa restoredOutput s = some s' ∧
      s'.mem = s.mem.writeW (addr32 (dataArg s)) (byteRev64 (finalWord s)) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .edx → s'.gpr r = s.gpr r) := by
  have hw0 := hw 0 (by decide)
  have hw1 := hw 1 (by decide)
  have h24 := hr 24 (by decide)
  have h28 := hr 28 (by decide)
  simp only [wordAddr, addr, dataArg] at harg hw0 hw1
  simp only [addr] at h24 h28
  refine ⟨_, by
    simp only [restoredOutput, rr, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc,
      State.load32, State.store32, State.ea, memOp, harg, hw0, hw1, h24, h28, ite_true,
      Option.map_some, gpr_setReg, mem_setReg, rd_setReg, wr_setReg,
      reduceCtorEq, ite_false]
    rfl, ?_, ?_, ?_, ?_⟩
  · dsimp only [mem_setReg, gpr_setReg, reduceCtorEq, ite_true, ite_false]
    have ha0 : (dataArg s + BitVec.ofNat 32 0).setWidth 64 = addr32 (dataArg s) := by simp [addr32]
    have ha1 : (dataArg s + BitVec.ofNat 32 4).setWidth 64 = addr32 (dataArg s) + 4 := addr_eq (by omega)
    change (s.mem.writeW ((dataArg s + BitVec.ofNat 32 0).setWidth 64)
      (bswap (s.mem.readW (addr (s.gpr .eax) 28) 32))).writeW
      ((dataArg s + BitVec.ofNat 32 4).setWidth 64)
      (bswap (s.mem.readW (addr (s.gpr .eax) 24) 32)) = _
    rw [ha0, ha1, writeW_pair, bswapPair]
    rfl
  · rfl
  · rfl
  · intro r ha hc hd
    simp only [gpr_setReg, ha, hc, hd, ite_false]

end VG.Proof.TripleDes.X86
