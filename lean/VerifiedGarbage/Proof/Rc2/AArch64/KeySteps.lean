import VerifiedGarbage.Impl.Rc2.AArch64.ExpandKey
import VerifiedGarbage.Proof.Rc2.AArch64.BlockIO
import VerifiedGarbage.Proof.Framework.AArch64.Spill
import VerifiedGarbage.Proof.Rc2.Expansion

/-! # Individual AArch64 RC2 key-expansion steps -/

namespace VG.Proof.Rc2.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.Rc2.AArch64

def keyTemps : List Reg := [.x8, .x23, .x3, .x5, .x6, .x7, .x9, .x10]

/-- The public comparison register represents the loop's zero test. -/
def zeroFlag (s : State) : Option Bool := some (s.gpr .x10 == 0)

theorem eval_zero (s : State) : eval (.zero .x .x10) s = zeroFlag s := rfl

theorem eval_nonzero (s : State) :
    eval (.nonzero .x .x10) s = (zeroFlag s).map (!·) := rfl

theorem copyKey_ok (s : State)
    (readable : InRegions (s.rd ++ s.wr) (s.gpr .x19 + s.gpr .x23) 1)
    (writable : InRegions s.wr (s.gpr .x21 + s.gpr .x23) 1) :
    ∃ s', runBlock isa copyKey s = some s' ∧
      s'.gpr .x23 = s.gpr .x23 + 1 ∧
      zeroFlag s' = some ((s.gpr .x23 + 1 - s.gpr .x20) == 0) ∧
      Keep keyTemps
        {s with mem := s.mem.writeW (s.gpr .x21 + s.gpr .x23) (s.mem (s.gpr .x19 + s.gpr .x23))} s' := by
  refine ⟨_, by
    simp (config := {decide := true}) only [copyKey, runBlock_cons, runStep_some,
      runBlock_nil, exec, State.read, State.load, State.store, addr, readByte,
      BitVec.add_zero, Option.map_some, Option.bind_some, gpr_write, BitVec.setWidth_eq,
      mem_write, rd_write, wr_write, readable, writable, ite_true, ite_false]
    rfl, ?_⟩
  refine ⟨?_, ?_, ?_⟩
  · simp only [gpr_write, BitVec.setWidth_eq, reduceCtorEq, ite_false, ite_true]
    rfl
  · simp only [zeroFlag, gpr_write_self, BitVec.setWidth_eq]
    rfl
  · constructor
    · intro r hr
      have h8 : r ≠ .x8 := by intro h; subst r; exact hr (by decide)
      have h23 : r ≠ .x23 := by intro h; subst r; exact hr (by decide)
      have h9 : r ≠ .x9 := by intro h; subst r; exact hr (by decide)
      have h10 : r ≠ .x10 := by intro h; subst r; exact hr (by decide)
      simp only [gpr_write, BitVec.setWidth_eq, h8, h23, h9, h10, ite_false]
    · simp only [mem_write, BitVec.setWidth_setWidth_of_le _ (show 8 ≤ 64 by decide),
        BitVec.setWidth_setWidth_of_le _ (show 8 ≤ 32 by decide), BitVec.setWidth_eq]
      rfl
    · rfl
    · rfl

theorem fillInput_ok (s : State)
    (readLo : InRegions (s.rd ++ s.wr) (s.gpr .x21 + s.gpr .x23 - 1#64) 1)
    (readHi : InRegions (s.rd ++ s.wr) (s.gpr .x21 + (s.gpr .x23 - s.gpr .x20)) 1) :
    ∃ s', runBlock isa fillInput s = some s' ∧
      s'.gpr .x8 = (s.mem (s.gpr .x21 + s.gpr .x23 - 1#64)).setWidth 64 +
        (s.mem (s.gpr .x21 + (s.gpr .x23 - s.gpr .x20))).setWidth 64 ∧
      Keep [.x8, .x3, .x5, .x9] s s' := by
  refine ⟨_, by
    simp (config := {decide := true}) only [fillInput, runBlock_cons, runStep_some,
      runBlock_nil, exec, State.read, State.load, addr, readByte,
      BitVec.add_zero, Option.map_some, Option.bind_some, gpr_write, BitVec.setWidth_eq,
      mem_write, rd_write, wr_write, readLo, readHi, ite_true, ite_false]
    rfl, ?_⟩
  constructor
  · simp only [gpr_write_self, BitVec.setWidth_eq,
      BitVec.setWidth_setWidth (by decide : ¬(32 < 8 ∧ 32 < 64))]
  · constructor
    · intro r hr
      have h8 : r ≠ .x8 := by intro h; subst r; exact hr (by decide)
      have h3 : r ≠ .x3 := by intro h; subst r; exact hr (by decide)
      have h5 : r ≠ .x5 := by intro h; subst r; exact hr (by decide)
      have h9 : r ≠ .x9 := by intro h; subst r; exact hr (by decide)
      simp only [gpr_write, BitVec.setWidth_eq, h8, h3, h5, h9, ite_false]
    · rfl
    · rfl
    · rfl

theorem fillOutput_ok (s : State)
    (writable : InRegions s.wr (s.gpr .x21 + s.gpr .x23) 1) :
    ∃ s', runBlock isa fillFinish s = some s' ∧
      s'.gpr .x23 = s.gpr .x23 + 1 ∧
      zeroFlag s' = some ((s.gpr .x23 + 1 - 128) == 0) ∧
      Keep keyTemps {s with mem := s.mem.writeW (s.gpr .x21 + s.gpr .x23) ((s.gpr .x8).setWidth 8)} s' := by
  refine ⟨_, by
    simp (config := {decide := true}) only [fillFinish, storeKey, List.cons_append, List.nil_append, runBlock_cons, runStep_some,
      runBlock_nil, exec, State.read, State.store, addr,
      BitVec.add_zero, Option.bind_some, gpr_write, BitVec.setWidth_eq,
      mem_write, rd_write, wr_write, writable, ite_true, ite_false]
    rfl, ?_⟩
  refine ⟨?_, ?_, ?_⟩
  · simp only [gpr_write, BitVec.setWidth_eq, reduceCtorEq, ite_true, ite_false]
    rfl
  · simp only [zeroFlag, gpr_write_self, BitVec.setWidth_eq]
    rfl
  · constructor
    · intro r hr
      have h23 : r ≠ .x23 := by intro h; subst r; exact hr (by decide)
      have h9 : r ≠ .x9 := by intro h; subst r; exact hr (by decide)
      have h10 : r ≠ .x10 := by intro h; subst r; exact hr (by decide)
      simp only [gpr_write, BitVec.setWidth_eq, h23, h9, h10, ite_false]
    · simp only [mem_write, BitVec.setWidth_setWidth_of_le _ (show 8 ≤ 32 by decide)]
      rfl
    · rfl
    · rfl

theorem reduceInput_ok (s : State)
    (readable : InRegions (s.rd ++ s.wr) (s.gpr .x21 + s.gpr .x23) 1) :
    ∃ s', runBlock isa reduceInput s = some s' ∧
      s'.gpr .x8 = (s.mem (s.gpr .x21 + s.gpr .x23)).setWidth 64 &&& s.gpr .x2 ∧
      Keep [.x8, .x9] s s' := by
  refine ⟨_, by
    simp (config := {decide := true}) only [reduceInput, runBlock_cons, runStep_some,
      runBlock_nil, exec, State.read, State.load, addr, readByte,
      BitVec.add_zero, Option.map_some, Option.bind_some, gpr_write, BitVec.setWidth_eq,
      mem_write, rd_write, wr_write, readable, ite_true, ite_false]
    rfl, ?_⟩
  constructor
  · simp only [gpr_write_self, BitVec.setWidth_eq,
      BitVec.setWidth_setWidth (by decide : ¬(32 < 8 ∧ 32 < 64))]
  · constructor
    · intro r hr
      have h8 : r ≠ .x8 := by intro h; subst r; exact hr (by decide)
      have h9 : r ≠ .x9 := by intro h; subst r; exact hr (by decide)
      simp only [gpr_write, BitVec.setWidth_eq, h8, h9, ite_false]
    · rfl
    · rfl
    · rfl

theorem storeByte_ok (s : State)
    (writable : InRegions s.wr (s.gpr .x21 + s.gpr .x23) 1) :
    ∃ s', runBlock isa storeKey s = some s' ∧ s'.gpr .x23 = s.gpr .x23 ∧
      Keep [.x9] {s with mem := s.mem.writeW (s.gpr .x21 + s.gpr .x23) ((s.gpr .x8).setWidth 8)} s' := by
  refine ⟨_, by
    simp (config := {decide := true}) only [storeKey, runBlock_cons, runStep_some,
      runBlock_nil, exec, State.read, State.store, addr,
      BitVec.add_zero, Option.bind_some, gpr_write, BitVec.setWidth_eq,
      mem_write, rd_write, wr_write, writable, ite_true, ite_false]
    rfl, ?_⟩
  constructor
  · rfl
  · constructor
    · intro r hr
      have h9 : r ≠ .x9 := by intro h; subst r; exact hr (by decide)
      simp only [gpr_write, BitVec.setWidth_eq, h9, ite_false]
    · simp only [BitVec.setWidth_setWidth_of_le _ (show 8 ≤ 32 by decide)]
      rfl
    · rfl
    · rfl

theorem descendInput_ok (s : State)
    (readLo : InRegions (s.rd ++ s.wr) (s.gpr .x21 + (s.gpr .x23 - 1#64) + 1#64) 1)
    (readHi : InRegions (s.rd ++ s.wr) (s.gpr .x21 + (s.gpr .x23 - 1#64 + s.gpr .x24)) 1) :
    ∃ s', runBlock isa descendInput s = some s' ∧
      s'.gpr .x23 = s.gpr .x23 - 1 ∧
      s'.gpr .x8 = (s.mem (s.gpr .x21 + (s.gpr .x23 - 1#64) + 1#64)).setWidth 64 ^^^
        (s.mem (s.gpr .x21 + (s.gpr .x23 - 1#64 + s.gpr .x24))).setWidth 64 ∧
      Keep [.x8, .x23, .x3, .x5, .x9] s s' := by
  refine ⟨_, by
    simp (config := {decide := true}) only [descendInput, runBlock_cons, runStep_some,
      runBlock_nil, exec, State.read, State.load, addr, readByte,
      BitVec.add_zero, Option.map_some, Option.bind_some, gpr_write, BitVec.setWidth_eq,
      mem_write, rd_write, wr_write, readLo, readHi, ite_true, ite_false]
    rfl, ?_⟩
  refine ⟨?_, ?_, ?_⟩
  · simp only [gpr_write, BitVec.setWidth_eq, reduceCtorEq, ite_true, ite_false]
    rfl
  · simp only [gpr_write_self, BitVec.setWidth_eq,
      BitVec.setWidth_setWidth (by decide : ¬(32 < 8 ∧ 32 < 64))]
  · constructor
    · intro r hr
      have h8 : r ≠ .x8 := by intro h; subst r; exact hr (by decide)
      have h23 : r ≠ .x23 := by intro h; subst r; exact hr (by decide)
      have h3 : r ≠ .x3 := by intro h; subst r; exact hr (by decide)
      have h5 : r ≠ .x5 := by intro h; subst r; exact hr (by decide)
      have h9 : r ≠ .x9 := by intro h; subst r; exact hr (by decide)
      simp only [gpr_write, BitVec.setWidth_eq, h8, h23, h3, h5, h9, ite_false]
    · rfl
    · rfl
    · rfl

theorem cmpZero_ok (s : State) :
    ∃ s', runBlock isa [rr .x10 .x23] s = some s' ∧
      zeroFlag s' = some (s.gpr .x23 == 0) ∧ Keep [.x10] s s' := by
  refine ⟨s.write .x .x10 (s.gpr .x23), ?_, ?_⟩
  · simp only [rr, runBlock_cons, exec, show 0 < 4096 by decide, ite_true,
      State.read, BitVec.setWidth_eq, BitVec.add_zero, runStep_some, runBlock_nil]
  constructor
  · rfl
  · exact ⟨fun r hr => gpr_write_of_ne _ _ _ (by simpa using hr), rfl, rfl, rfl⟩

end VG.Proof.Rc2.AArch64
