import VerifiedGarbage.Proof.Rc2.X86.BlockStore

namespace VG.Proof.Rc2.X86

open VG VG.X86 VG.X86.RegUpd VG.Impl.Rc2.X86

theorem argContainsCount (s : State) (count : Nat) (fit : (s.gpr .esp).toNat + 4 + 4 * count ≤ 2 ^ 32)
    (i : Nat) (hi : i < count) :
    (Region.mk (argAddr s 0) (4 * count)).Contains
      (addr32 (s.gpr .esp) + BitVec.ofNat 64 (4 + 4 * i)) 4 := by
  rw [argAddr_eq s 0 (by omega)]
  exact Offset.contains _ (by omega) (by omega) (by omega)

theorem arguments_frame (count : Nat) {s s' : State} {rs : List Region}
    (frame : Frame rs s.mem s'.mem) (sp : s'.gpr .esp = s.gpr .esp)
    (fit : (s.gpr .esp).toNat + 4 + 4 * count ≤ 2 ^ 32)
    (sep : ∀ r ∈ rs, (Region.mk (argAddr s 0) (4 * count)).Disjoint r) :
    ∀ i < count, arg s' i = arg s i := by
  intro i hi
  unfold arg
  have e : argAddr s' i = argAddr s i := by unfold argAddr; rw [sp]
  rw [e, argAddr_eq s i (by omega)]
  exact frame.readW (argContainsCount s count fit i hi) sep (by decide)

theorem pinBlock_ok (s : State)
    (readable : InRegions (s.rd ++ s.wr) (argAddr s 1) 4) :
    ∃ s', runBlock isa [rr .ebp .eax, .mov .edi (.mem (memOp .esp 8))] s = some s' ∧
      s'.gpr .ebp = s.gpr .eax ∧ s'.gpr .edi = arg s 1 ∧ Keep [.ebp, .edi] s s' := by
  simp only [argAddr, Nat.reduceMul, Nat.reduceAdd] at readable
  refine ⟨_, by
    simp (config := {decide := true}) only [rr, memOp, State.ea, runBlock_cons,
      runStep_some, runBlock_nil, exec, readSrc, State.load32, Option.map_some,
      gpr_setReg, mem_setReg, rd_setReg, wr_setReg, readable, ite_true, ite_false]
    rfl, ?_⟩
  refine ⟨?_, rfl, ?_⟩
  · simp only [gpr_setReg, reduceCtorEq, ite_false, ite_true]
  · constructor
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp only [gpr_setReg, hr.1, hr.2, ite_false]
    · rfl
    · rfl
    · rfl

theorem blockScratchBase_ok (s : State) :
    ∃ s', runBlock isa [rr .eax .ebp] s = some s' ∧
      s'.gpr .eax = s.gpr .ebp ∧ Keep [.eax] s s' := by
  refine ⟨s.setReg .eax (s.gpr .ebp), rfl, rfl, ?_⟩
  exact ⟨fun r hr => gpr_setReg_of_ne _ _ (by simpa using hr), rfl, rfl, rfl⟩

end VG.Proof.Rc2.X86
