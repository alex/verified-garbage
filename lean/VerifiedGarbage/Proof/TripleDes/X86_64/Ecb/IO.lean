import VerifiedGarbage.Proof.TripleDes.X86_64.Ecb.Loop

namespace VG.Proof.TripleDes.X86_64.Ecb

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.TripleDes.X86_64
open VG.Proof.Rc2.X86_64 (Keep offset_nat)

def savedMem (s : State) : Mem :=
  s.mem.writeW (s.gpr .rcx + BitVec.ofNat 64 512) (s.gpr .rbp)

theorem save_ok (s : State)
    (hw : InRegions s.wr (s.gpr .rcx + BitVec.ofNat 64 512) 8) :
    ∃ s', runBlock isa Impl.TripleDes.X86_64.Ecb.save s = some s' ∧
      Keep [] {s with mem := savedMem s} s' := by
  refine ⟨_, by
    simp only [Impl.TripleDes.X86_64.Ecb.save, runBlock_cons, runStep_some, runBlock_nil,
      memOp, exec, State.store64, State.ea, offset_nat, hw, ite_true]
    rfl, ?_⟩
  exact ⟨fun _ _ => rfl, rfl, rfl, rfl⟩

theorem savedMem_frame (s : State) : Frame [⟨s.gpr .rcx, 1024⟩] s.mem (savedMem s) :=
  (Frame.refl _ _).writeW List.mem_cons_self _
    (Offset.contains_base _ (by decide : 512 + 8 ≤ 1024) (by decide))

theorem savedMem_rbp (s : State) : (savedMem s).readW (s.gpr .rcx + BitVec.ofNat 64 512) 64 = s.gpr .rbp := by
  rw [savedMem, Mem.readW_writeW_self64]

theorem setup_ok (s : State) :
    ∃ s', runBlock isa Impl.TripleDes.X86_64.Ecb.setup s = some s' ∧
      s'.gpr .rbp = s.gpr .rdx ∧ s'.gpr .rdx = s.gpr .rcx ∧
      s'.zf = some (s.gpr .rdx == 0) ∧ Keep [.rbp, .rdx] s s' := by
  refine ⟨_, by
    simp only [Impl.TripleDes.X86_64.Ecb.setup, rr, runBlock_cons, exec, readSrc]
    rfl, ?_⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [gpr_arithFlags, gpr_setReg, reduceCtorEq, ite_true, ite_false]
  · simp only [gpr_arithFlags, gpr_setReg, reduceCtorEq, ite_true, ite_false]
  · rw [zf_arithFlags]
    simp only [gpr_setReg, reduceCtorEq, ite_false, ite_true]
    rw [show (0 : BitVec 32).signExtend 64 = (0 : BitVec 64) by rfl]
    exact congrArg (fun x : BitVec 64 => some (x == 0)) (BitVec.sub_zero _)
  · constructor
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp only [gpr_setReg, gpr_arithFlags, hr.1, hr.2, ite_false]
    · simp only [mem_setReg, mem_arithFlags]
    · simp only [rd_setReg, rd_arithFlags]
    · simp only [wr_setReg, wr_arithFlags]

theorem restore_ok (s : State) (v : BitVec 64)
    (hr : InRegions (s.rd ++ s.wr) (s.gpr .rdx + BitVec.ofNat 64 512) 8)
    (hv : s.mem.readW (s.gpr .rdx + BitVec.ofNat 64 512) 64 = v) :
    ∃ s', runBlock isa Impl.TripleDes.X86_64.Ecb.restore s = some s' ∧
      s'.gpr .rbp = v ∧ Keep [.rbp] s s' := by
  refine ⟨_, by
    simp only [Impl.TripleDes.X86_64.Ecb.restore, runBlock_cons, runStep_some,
      runBlock_nil, memOp, exec, readSrc, State.load64, State.ea, offset_nat, hr, ite_true,
      Option.map_some, hv]
    rfl, gpr_setReg_self _ _ _, ?_⟩
  exact ⟨fun r h => gpr_setReg_of_ne _ _ (by simpa only [List.mem_singleton] using h), rfl, rfl, rfl⟩

theorem LoopPost.scratchRead {d : Spec.TripleDes.Direction} {s s' : State} {n : Nat}
    (h : LoopPost d s n s') (hp : StepPre s n) :
    s'.mem.readW (s.gpr .rdx + BitVec.ofNat 64 512) 64 =
      s.mem.readW (s.gpr .rdx + BitVec.ofNat 64 512) 64 := by
  have sub : Region.Sub ⟨s.gpr .rdx + BitVec.ofNat 64 512, 8⟩ (bufR s) :=
    Offset.sub_base _ (by decide)
  have sep : (Region.mk (s.gpr .rdx + BitVec.ofNat 64 512) 8).Disjoint ⟨s.gpr .rdx, 512⟩ :=
    Offset.disjoint_base _ (by decide) (by decide)
  apply h.mem.readW (r := ⟨s.gpr .rdx + BitVec.ofNat 64 512, 8⟩) (Region.contains_self _ _)
    (hn := by decide)
  simpa only [loopWrites, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] using
    And.intro ((hp.dataBuf.sub_right sub).symm) (And.intro sep ((hp.stackBuf.sub_right sub).symm))

end VG.Proof.TripleDes.X86_64.Ecb
