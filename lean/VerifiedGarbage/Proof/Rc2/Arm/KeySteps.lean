import VerifiedGarbage.Impl.Rc2.Arm.ExpandKey
import VerifiedGarbage.Proof.Rc2.Arm.Save
import VerifiedGarbage.Proof.Rc2.Expansion

/-! # Individual Arm RC2 key-expansion steps -/

namespace VG.Proof.Rc2.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.Rc2.Arm VG.Proof.Rc2.Word32

def keyTemps : List Reg := [.r12, .r0, .r3, .r9, .r10, .r11, .lr]

/-- The public zero flag controls the key-expansion loops. -/
def zeroFlag (s : State) : Option Bool := some s.z

theorem eval_zero (s : State) : eval .eq s = zeroFlag s := rfl

theorem eval_nonzero (s : State) :
    eval .ne s = (zeroFlag s).map (!·) := rfl

theorem gpr_subFlags (s : State) (x y : BitVec 32) (r : Reg) :
    (subFlags s x y).gpr r = s.gpr r := rfl

theorem mem_subFlags (s : State) (x y : BitVec 32) : (subFlags s x y).mem = s.mem := rfl

theorem rd_subFlags (s : State) (x y : BitVec 32) : (subFlags s x y).rd = s.rd := rfl

theorem wr_subFlags (s : State) (x y : BitVec 32) : (subFlags s x y).wr = s.wr := rfl

theorem zeroFlag_subFlags (s : State) (x y : BitVec 32) :
    zeroFlag (subFlags s x y) = some (x - y == 0) := rfl

theorem copyKey_ok (s : State)
    (readable : InRegions (s.rd ++ s.wr) (State.addr (s.gpr .r4 + s.gpr .r0)) 1)
    (writable : InRegions s.wr (State.addr (s.gpr .r6 + s.gpr .r0)) 1) :
    ∃ s', runBlock isa copyKey s = some s' ∧
      s'.gpr .r0 = s.gpr .r0 + 1 ∧
      zeroFlag s' = some ((s.gpr .r0 + 1 - s.gpr .r5) == 0) ∧
      Keep keyTemps
        {s with mem := s.mem.writeW (State.addr (s.gpr .r6 + s.gpr .r0)) (s.mem (State.addr (s.gpr .r4 + s.gpr .r0)))} s' := by
  refine ⟨_, by
    simp (config := {decide := true}) only [copyKey, runBlock_cons, runStep_some,
      runBlock_nil, exec, Op2.eval, Option.map_some, State.load8, State.store8,
      BitVec.add_zero, gpr_setReg,
      mem_setReg, rd_setReg, wr_setReg, readable, writable, ite_true, ite_false]
    rfl, ?_⟩
  refine ⟨?_, ?_, ?_⟩
  · simp only [gpr_setReg, gpr_subFlags, reduceCtorEq, ite_false, ite_true]
  · simp only [zeroFlag_subFlags]
  · constructor
    · intro r hr
      have h8 : r ≠ .r12 := by intro h; subst r; exact hr (by decide)
      have h23 : r ≠ .r0 := by intro h; subst r; exact hr (by decide)
      have h9 : r ≠ .lr := by intro h; subst r; exact hr (by decide)
      simp only [gpr_setReg, gpr_subFlags, h8, h23, h9, ite_false]
    · simp only [mem_subFlags, mem_setReg,
        BitVec.setWidth_setWidth_of_le _ (show 8 ≤ 32 by decide), BitVec.setWidth_eq]
    · rfl
    · rfl

theorem fillInput_ok (s : State)
    (readLo : InRegions (s.rd ++ s.wr) (State.addr (s.gpr .r6 + s.gpr .r0 - 1)) 1)
    (readHi : InRegions (s.rd ++ s.wr) (State.addr (s.gpr .r6 + (s.gpr .r0 - s.gpr .r5))) 1) :
    ∃ s', runBlock isa fillInput s = some s' ∧
      s'.gpr .r12 = (s.mem (State.addr (s.gpr .r6 + s.gpr .r0 - 1))).setWidth 32 +
        (s.mem (State.addr (s.gpr .r6 + (s.gpr .r0 - s.gpr .r5)))).setWidth 32 ∧
      Keep [.r12, .r3, .r9, .lr] s s' := by
  refine ⟨_, by
    simp (config := {decide := true}) only [fillInput, runBlock_cons, runStep_some,
      runBlock_nil, exec, Op2.eval, Option.map_some, State.load8,
      BitVec.add_zero, gpr_setReg,
      mem_setReg, rd_setReg, wr_setReg, readLo, readHi, ite_true, ite_false]
    rfl, ?_⟩
  constructor
  · simp only [gpr_setReg_self]
  · constructor
    · intro r hr
      have h8 : r ≠ .r12 := by intro h; subst r; exact hr (by decide)
      have h3 : r ≠ .r3 := by intro h; subst r; exact hr (by decide)
      have h5 : r ≠ .r9 := by intro h; subst r; exact hr (by decide)
      have h9 : r ≠ .lr := by intro h; subst r; exact hr (by decide)
      simp only [gpr_setReg, h8, h3, h5, h9, ite_false]
    · rfl
    · rfl
    · rfl

theorem fillOutput_ok (s : State)
    (writable : InRegions s.wr (State.addr (s.gpr .r6 + s.gpr .r0)) 1) :
    ∃ s', runBlock isa fillFinish s = some s' ∧
      s'.gpr .r0 = s.gpr .r0 + 1 ∧
      zeroFlag s' = some ((s.gpr .r0 + 1 - 128) == 0) ∧
      Keep keyTemps {s with mem := s.mem.writeW (State.addr (s.gpr .r6 + s.gpr .r0)) ((s.gpr .r12).setWidth 8)} s' := by
  refine ⟨_, by
    simp (config := {decide := true}) only [fillFinish, storeKey, List.cons_append, List.nil_append, runBlock_cons, runStep_some,
      runBlock_nil, exec, Op2.eval, Option.map_some, State.store8,
      BitVec.add_zero, gpr_setReg,
      mem_setReg, rd_setReg, wr_setReg, writable, ite_true, ite_false]
    rfl, ?_⟩
  refine ⟨?_, ?_, ?_⟩
  · simp only [gpr_setReg, gpr_subFlags, reduceCtorEq, ite_true, ite_false]
  · simp only [zeroFlag_subFlags]
  · constructor
    · intro r hr
      have h23 : r ≠ .r0 := by intro h; subst r; exact hr (by decide)
      have h9 : r ≠ .lr := by intro h; subst r; exact hr (by decide)
      simp only [gpr_setReg, gpr_subFlags, h23, h9, ite_false]
    · simp only [mem_subFlags, mem_setReg]
    · rfl
    · rfl

theorem reduceInput_ok (s : State)
    (readable : InRegions (s.rd ++ s.wr) (State.addr (s.gpr .r6 + s.gpr .r0)) 1) :
    ∃ s', runBlock isa reduceInput s = some s' ∧
      s'.gpr .r12 = (s.mem (State.addr (s.gpr .r6 + s.gpr .r0))).setWidth 32 &&& s.gpr .r2 ∧
      Keep [.r12, .lr] s s' := by
  refine ⟨_, by
    simp (config := {decide := true}) only [reduceInput, runBlock_cons, runStep_some,
      runBlock_nil, exec, Op2.eval, Option.map_some, State.load8,
      BitVec.add_zero, gpr_setReg,
      mem_setReg, rd_setReg, wr_setReg, readable, ite_true, ite_false]
    rfl, ?_⟩
  constructor
  · simp only [gpr_setReg_self]
  · constructor
    · intro r hr
      have h8 : r ≠ .r12 := by intro h; subst r; exact hr (by decide)
      have h9 : r ≠ .lr := by intro h; subst r; exact hr (by decide)
      simp only [gpr_setReg, h8, h9, ite_false]
    · rfl
    · rfl
    · rfl

theorem storeByte_ok (s : State)
    (writable : InRegions s.wr (State.addr (s.gpr .r6 + s.gpr .r0)) 1) :
    ∃ s', runBlock isa storeKey s = some s' ∧ s'.gpr .r0 = s.gpr .r0 ∧
      Keep [.lr] {s with mem := s.mem.writeW (State.addr (s.gpr .r6 + s.gpr .r0)) ((s.gpr .r12).setWidth 8)} s' := by
  refine ⟨_, by
    simp (config := {decide := true}) only [storeKey, runBlock_cons, runStep_some,
      runBlock_nil, exec, Op2.eval, Option.map_some, State.store8,
      BitVec.add_zero, gpr_setReg,
      mem_setReg, rd_setReg, wr_setReg, writable, ite_true, ite_false]
    rfl, ?_⟩
  constructor
  · rfl
  · constructor
    · intro r hr
      have h9 : r ≠ .lr := by intro h; subst r; exact hr (by decide)
      simp only [gpr_setReg, h9, ite_false]
    · rfl
    · rfl
    · rfl

theorem descendInput_ok (s : State)
    (readLo : InRegions (s.rd ++ s.wr) (State.addr (s.gpr .r6 + (s.gpr .r0 - 1) + 1)) 1)
    (readHi : InRegions (s.rd ++ s.wr) (State.addr (s.gpr .r6 + (s.gpr .r0 - 1 + s.gpr .r1))) 1) :
    ∃ s', runBlock isa descendInput s = some s' ∧
      s'.gpr .r0 = s.gpr .r0 - 1 ∧
      s'.gpr .r12 = (s.mem (State.addr (s.gpr .r6 + (s.gpr .r0 - 1) + 1))).setWidth 32 ^^^
        (s.mem (State.addr (s.gpr .r6 + (s.gpr .r0 - 1 + s.gpr .r1)))).setWidth 32 ∧
      Keep [.r12, .r0, .r3, .r9, .lr] s s' := by
  refine ⟨_, by
    simp (config := {decide := true}) only [descendInput, runBlock_cons, runStep_some,
      runBlock_nil, exec, Op2.eval, Option.map_some, State.load8,
      BitVec.add_zero, gpr_setReg,
      mem_setReg, rd_setReg, wr_setReg, readLo, readHi, ite_true, ite_false]
    rfl, ?_⟩
  refine ⟨?_, ?_, ?_⟩
  · simp only [gpr_setReg, reduceCtorEq, ite_true, ite_false]
  · simp only [gpr_setReg_self]
  · constructor
    · intro r hr
      have h8 : r ≠ .r12 := by intro h; subst r; exact hr (by decide)
      have h23 : r ≠ .r0 := by intro h; subst r; exact hr (by decide)
      have h3 : r ≠ .r3 := by intro h; subst r; exact hr (by decide)
      have h5 : r ≠ .r9 := by intro h; subst r; exact hr (by decide)
      have h9 : r ≠ .lr := by intro h; subst r; exact hr (by decide)
      simp only [gpr_setReg, h8, h23, h3, h5, h9, ite_false]
    · rfl
    · rfl
    · rfl

theorem cmpZero_ok (s : State) :
    ∃ s', runBlock isa [.cmp .r0 (.imm 0)] s = some s' ∧
      zeroFlag s' = some (s.gpr .r0 == 0) ∧ Keep [] s s' := by
  refine ⟨subFlags s (s.gpr .r0) 0, ?_, ?_⟩
  · simp (config := {decide := true}) only [runBlock_cons, exec, Op2.eval,
      ite_true, Option.map_some, runStep_some, runBlock_nil]
  constructor
  · exact congrArg (fun x : BitVec 32 => some (x == 0)) (by bv_omega)
  · exact ⟨fun _ _ => rfl, rfl, rfl, rfl⟩

end VG.Proof.Rc2.Arm
