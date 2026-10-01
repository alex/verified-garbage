import VerifiedGarbage.Proof.Rc2.Arm.KeyBody
import VerifiedGarbage.Proof.Rc2.Arm.Save
import VerifiedGarbage.Proof.Framework.Arm.Contract

/-! # Register setup and scratch saves for key expansion -/

namespace VG.Proof.Rc2.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.Rc2.Arm VG.Proof.Rc2.Word32

def savedReg (i : Nat) : Reg := saved.getD i .r0

theorem keySave_eq : save .r12 0 = saveCode .r12 savedReg 9 := by rfl

theorem keyRestore_eq : restore .r12 0 = restoreCode .r12 savedReg (List.range 9) := by rfl

theorem pinKey_ok (s : State) :
    ∃ s', runBlock isa [rr .r8 .r12, rr .r4 .r0, rr .r5 .r1, rr .r6 .r3, rr .r7 .r2, imm .r0 0] s = some s' ∧
      s'.gpr .r8 = s.gpr .r12 ∧ s'.gpr .r4 = s.gpr .r0 ∧ s'.gpr .r5 = s.gpr .r1 ∧
      s'.gpr .r6 = s.gpr .r3 ∧ s'.gpr .r7 = s.gpr .r2 ∧ s'.gpr .r0 = 0 ∧ Keep [.r8, .r4, .r5, .r6, .r7, .r0] s s' := by
  refine ⟨_, by
    simp only [rr, imm, runBlock_cons, exec]
    rfl, ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [gpr_setReg]
  · simp [gpr_setReg]
  · simp [gpr_setReg]
  · simp [gpr_setReg]
  · simp [gpr_setReg]
  · exact gpr_setReg_self _ _ _
  · constructor
    · intro r hr
      have sep : r ≠ .r8 ∧ r ≠ .r4 ∧ r ≠ .r5 ∧ r ≠ .r6 ∧ r ≠ .r7 ∧ r ≠ .r0 := by
        simpa only [List.mem_cons, List.not_mem_nil, or_false, not_or] using hr
      simp only [gpr_setReg, sep.1, sep.2.1, sep.2.2.1, sep.2.2.2.1,
        sep.2.2.2.2.1, sep.2.2.2.2.2, ite_false]
    · rfl
    · rfl
    · rfl

theorem loadScratch_ok (s : State)
    (readable : InRegions (s.rd ++ s.wr) (stackArgAddr s 0) 4) :
    ∃ s', runBlock isa [.ldrSp .r12 0] s = some s' ∧
      s'.gpr .r12 = stackArg s 0 ∧ Keep [.r12] s s' := by
  have rd : InRegions (s.rd ++ s.wr) (State.addr s.sp) 4 := by
    simpa only [stackArgAddr, Nat.mul_zero, BitVec.add_zero] using readable
  refine ⟨s.setReg .r12 (stackArg s 0), ?_, ?_⟩
  · simp (config := {decide := true}) only [runBlock_cons, exec,
      State.load32, rd, ite_true, BitVec.add_zero,
      Option.map_some, runStep_some, runBlock_nil, stackArg, stackArgAddr, Nat.mul_zero]
  · exact ⟨rfl, fun r hr => gpr_setReg_of_ne _ _ (by simpa using hr), rfl, rfl, rfl⟩

theorem scratchBase_ok (s : State) :
    ∃ s', runBlock isa [rr .r12 .r8] s = some s' ∧
      s'.gpr .r12 = s.gpr .r8 ∧ Keep [.r12] s s' := by
  refine ⟨s.setReg .r12 (s.gpr .r8), rfl, rfl, ?_⟩
  exact ⟨fun r hr => gpr_setReg_of_ne _ _ (by simpa using hr), rfl, rfl, rfl⟩

theorem bytesAt_frame {m m' : Mem} {p : Addr} {n : Nat} {rs : List Region}
    (frame : Frame rs m m') (sep : ∀ r ∈ rs, (Region.mk p n).Disjoint r) (bound : n ≤ 2 ^ 64) :
    Spec.Rc2.bytesAt m' p n = Spec.Rc2.bytesAt m p n := by
  unfold Spec.Rc2.bytesAt
  apply List.map_congr_left
  intro i hi
  exact frame.bytes sep bound (List.mem_range.mp hi)

end VG.Proof.Rc2.Arm
