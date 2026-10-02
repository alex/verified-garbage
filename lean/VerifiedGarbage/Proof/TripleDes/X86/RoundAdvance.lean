import VerifiedGarbage.Proof.TripleDes.X86.RoundBody

namespace VG.Proof.TripleDes.X86
open VG VG.X86 VG.X86.Straight VG.X86.RegUpd VG.Impl.TripleDes.X86

def roundCount (s : State) : BitVec 32 := s.mem.readW (wordAddr (s.gpr .ebp) 5) 32

def nextPtr (d : Spec.TripleDes.Direction) (s : State) : BitVec 32 :=
  if d = .encrypt then roundKeyPtr s + 8 else roundKeyPtr s - 8

def advanceMem (d : Spec.TripleDes.Direction) (s : State) : Mem :=
  (s.mem.writeW (wordAddr (s.gpr .ebp) 4) (nextPtr d s)).writeW
    (wordAddr (s.gpr .ebp) 5) (roundCount s - 1)

theorem counter_ptr_sep (s : State) (fit : (s.gpr .ebp).toNat + 512 ≤ 2 ^ 32) :
    Mem.Sep (wordAddr (s.gpr .ebp) 5) 4 (wordAddr (s.gpr .ebp) 4) 4 := by
  change Mem.Sep (addr (s.gpr .ebp) 20) 4 (addr (s.gpr .ebp) 16) 4
  rw [addr_eq (by omega), addr_eq (by omega)]
  exact Offset.sep _ (by decide) (by decide) (by decide)

theorem roundAdvance_ok (d : Spec.TripleDes.Direction) (s : State) (hok : Ok sboxCfg s) :
    ∃ s', runBlock isa (roundAdvance d) s = some s' ∧
      s'.mem = advanceMem d s ∧ s'.zf = some ((roundCount s - 1) == 0) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r, r ≠ .eax → s'.gpr r = s.gpr r) := by
  have hw4 := hok.slotIn 4 (by decide)
  have hw5 := hok.slotIn 5 (by decide)
  have hr4 : InRegions (s.rd ++ s.wr) (wordAddr (s.gpr .ebp) 4) 4 := by
    obtain ⟨r, h, hc⟩ := hw4; exact ⟨r, List.mem_append_right _ h, hc⟩
  have hr5 : InRegions (s.rd ++ s.wr) (wordAddr (s.gpr .ebp) 5) 4 := by
    obtain ⟨r, h, hc⟩ := hw5; exact ⟨r, List.mem_append_right _ h, hc⟩
  have hsep := counter_ptr_sep s hok.fit
  simp only [wordAddr, addr, sboxCfg] at hw4 hw5 hr4 hr5 hsep
  cases d <;> refine ⟨_, by
    simp only [roundAdvance, reduceCtorEq, ite_true, ite_false, runBlock_cons,
      runStep_some, runBlock_nil, exec, execAlu, readSrc, State.load32, State.store32,
      State.ea, memOp, gpr_setReg, gpr_arithFlags, reduceCtorEq, ite_true, ite_false,
      mem_setReg, mem_arithFlags, rd_setReg, rd_arithFlags, wr_setReg, wr_arithFlags,
      hw4, hw5, hr4, hr5,
      Option.bind_some, Option.map_some]
    rfl, ?_, ?_, ?_, ?_, ?_⟩
  all_goals dsimp only [mem_setReg, mem_arithFlags, advanceMem, nextPtr, roundKeyPtr,
    roundCount, reduceCtorEq, ite_true, ite_false, wordAddr, addr,
    gpr_setReg, gpr_arithFlags,
    rd_setReg, wr_setReg, rd_arithFlags, wr_arithFlags, zf_setReg, zf_arithFlags]
  all_goals try rw [Mem.readW_writeW_sep hsep (by decide)]
  all_goals try rfl
  all_goals
    intro r hr
    simp only [hr, ite_false]
end VG.Proof.TripleDes.X86
