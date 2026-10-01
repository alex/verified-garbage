import VerifiedGarbage.Impl.Rc2.X86.ExpandKey
import VerifiedGarbage.Proof.Rc2.X86.Lookup
import VerifiedGarbage.Proof.Rc2.Expansion

/-! # Individual X86 RC2 key-expansion steps -/

namespace VG.Proof.Rc2.X86

open VG VG.X86 VG.X86.RegUpd VG.Impl.Rc2.X86 VG.Proof.Rc2.Word32

def addr32 (x : BitVec 32) : Addr := x.setWidth 64

theorem addr_add {x : BitVec 32} {k : Nat} (h : x.toNat + k < 2 ^ 32) :
    addr32 (x + BitVec.ofNat 32 k) = addr32 x + BitVec.ofNat 64 k :=
  VG.X86.addr_eq h

def keyTemps : List Reg := [.eax, .ecx, .ebx, .edx]

/-- The public zero flag controls the key-expansion loops. -/
def zeroFlag (s : State) : Option Bool := s.zf

theorem eval_zero (s : State) : eval .e s = zeroFlag s := rfl

theorem eval_nonzero (s : State) :
    eval .ne s = (zeroFlag s).map (!·) := rfl

theorem copyKey_ok (s : State)
    (readable : InRegions (s.rd ++ s.wr) (addr32 (s.gpr .ebp + s.gpr .ecx)) 1)
    (writable : InRegions s.wr (addr32 (s.gpr .edi + s.gpr .ecx)) 1) :
    ∃ s', runBlock isa copyKey s = some s' ∧
      s'.gpr .ecx = s.gpr .ecx + 1 ∧
      zeroFlag s' = some ((s.gpr .ecx + 1 - s.gpr .esi) == 0) ∧
      Keep keyTemps
        {s with mem := s.mem.writeW (addr32 (s.gpr .edi + s.gpr .ecx)) (s.mem (addr32 (s.gpr .ebp + s.gpr .ecx)))} s' := by
  simp only [addr32] at *
  refine ⟨_, by
    simp (config := {decide := true}) only [copyKey, runBlock_cons, runStep_some,
      runBlock_nil, exec, rr, memOp, State.ea, Reg8.reg, execAlu, readSrc, Option.bind_some, Option.map_some, State.load8, State.store8,
      BitVec.add_zero, gpr_setReg, gpr_arithFlags,
      mem_setReg, mem_arithFlags, rd_setReg, rd_arithFlags, wr_setReg, wr_arithFlags, readable, writable, ite_true, ite_false]
    rfl, ?_⟩
  refine ⟨?_, ?_, ?_⟩
  · simp only [gpr_setReg, gpr_arithFlags,  reduceCtorEq, ite_false, ite_true]
  · simp only [zeroFlag, zf_arithFlags, zf_setReg]
  · constructor
    · intro r hr
      have h8 : r ≠ .eax := by intro h; subst r; exact hr (by decide)
      have h23 : r ≠ .ecx := by intro h; subst r; exact hr (by decide)
      have h9 : r ≠ .edx := by intro h; subst r; exact hr (by decide)
      simp only [gpr_setReg, gpr_arithFlags,  h8, h23, h9, ite_false]
    · simp only [ mem_setReg, mem_arithFlags,
        BitVec.setWidth_setWidth_of_le _ (show 8 ≤ 32 by decide), BitVec.setWidth_eq]
    · rfl
    · rfl

theorem fillInput_ok (s : State)
    (readLo : InRegions (s.rd ++ s.wr) (addr32 (s.gpr .edi + s.gpr .ecx - 1)) 1)
    (readHi : InRegions (s.rd ++ s.wr) (addr32 (s.gpr .edi + (s.gpr .ecx - s.gpr .esi))) 1) :
    ∃ s', runBlock isa fillInput s = some s' ∧
      s'.gpr .eax = (s.mem (addr32 (s.gpr .edi + s.gpr .ecx - 1))).setWidth 32 +
        (s.mem (addr32 (s.gpr .edi + (s.gpr .ecx - s.gpr .esi)))).setWidth 32 ∧
      Keep [.eax, .ebx, .edx] s s' := by
  simp only [addr32] at *
  refine ⟨_, by
    simp (config := {decide := true}) only [fillInput, runBlock_cons, runStep_some,
      runBlock_nil, exec, rr, memOp, State.ea, execAlu, readSrc, Option.bind_some, Option.map_some, State.load8,
      BitVec.add_zero, gpr_setReg, gpr_arithFlags,
      mem_setReg, mem_arithFlags, rd_setReg, rd_arithFlags, wr_setReg, wr_arithFlags, readLo, readHi, ite_true, ite_false]
    rfl, ?_⟩
  constructor
  · simp only [gpr_setReg_self]
  · constructor
    · intro r hr
      have h8 : r ≠ .eax := by intro h; subst r; exact hr (by decide)
      have h3 : r ≠ .ebx := by intro h; subst r; exact hr (by decide)
      have h5 : r ≠ .edx := by intro h; subst r; exact hr (by decide)
      have h9 : r ≠ .edx := by intro h; subst r; exact hr (by decide)
      simp only [gpr_setReg, gpr_arithFlags, h8, h3, h5, ite_false]
    · rfl
    · rfl
    · rfl

theorem fillOutput_ok (s : State)
    (writable : InRegions s.wr (addr32 (s.gpr .edi + s.gpr .ecx)) 1) :
    ∃ s', runBlock isa fillFinish s = some s' ∧
      s'.gpr .ecx = s.gpr .ecx + 1 ∧
      zeroFlag s' = some ((s.gpr .ecx + 1 - 128) == 0) ∧
      Keep keyTemps {s with mem := s.mem.writeW (addr32 (s.gpr .edi + s.gpr .ecx)) ((s.gpr .eax).setWidth 8)} s' := by
  simp only [addr32] at *
  refine ⟨_, by
    simp (config := {decide := true}) only [fillFinish, storeKey, List.cons_append, List.nil_append, runBlock_cons, runStep_some,
      runBlock_nil, exec, rr, memOp, State.ea, Reg8.reg, execAlu, readSrc, Option.bind_some, Option.map_some, State.store8,
      BitVec.add_zero, gpr_setReg, gpr_arithFlags,
      mem_setReg, mem_arithFlags, rd_setReg, rd_arithFlags, wr_setReg, wr_arithFlags, writable, ite_true, ite_false]
    rfl, ?_⟩
  refine ⟨?_, ?_, ?_⟩
  · simp only [gpr_setReg, gpr_arithFlags,  reduceCtorEq, ite_true, ite_false]
  · simp only [zeroFlag, zf_arithFlags, zf_setReg]
  · constructor
    · intro r hr
      have h23 : r ≠ .ecx := by intro h; subst r; exact hr (by decide)
      have h9 : r ≠ .edx := by intro h; subst r; exact hr (by decide)
      simp only [gpr_setReg, gpr_arithFlags,  h23, h9, ite_false]
    · simp only [mem_arithFlags, mem_setReg]
    · rfl
    · rfl

theorem reduceInput_ok (s : State)
    (readable : InRegions (s.rd ++ s.wr) (addr32 (s.gpr .edi + s.gpr .ecx)) 1) :
    ∃ s', runBlock isa reduceInput s = some s' ∧
      s'.gpr .eax = (s.mem (addr32 (s.gpr .edi + s.gpr .ecx))).setWidth 32 &&& s.gpr .ebx ∧
      Keep [.eax, .edx] s s' := by
  simp only [addr32] at *
  refine ⟨_, by
    simp (config := {decide := true}) only [reduceInput, runBlock_cons, runStep_some,
      runBlock_nil, exec, rr, memOp, State.ea, execAlu, readSrc, Option.bind_some, Option.map_some, State.load8,
      BitVec.add_zero, gpr_setReg, gpr_arithFlags,
      mem_setReg, mem_arithFlags, rd_setReg, rd_arithFlags, wr_setReg, wr_arithFlags, readable, ite_true, ite_false]
    rfl, ?_⟩
  constructor
  · simp only [gpr_setReg_self]
  · constructor
    · intro r hr
      have h8 : r ≠ .eax := by intro h; subst r; exact hr (by decide)
      have h9 : r ≠ .edx := by intro h; subst r; exact hr (by decide)
      simp only [gpr_setReg, gpr_arithFlags, h8, h9, ite_false]
    · rfl
    · rfl
    · rfl

theorem storeByte_ok (s : State)
    (writable : InRegions s.wr (addr32 (s.gpr .edi + s.gpr .ecx)) 1) :
    ∃ s', runBlock isa storeKey s = some s' ∧ s'.gpr .ecx = s.gpr .ecx ∧
      Keep [.edx] {s with mem := s.mem.writeW (addr32 (s.gpr .edi + s.gpr .ecx)) ((s.gpr .eax).setWidth 8)} s' := by
  simp only [addr32] at *
  refine ⟨_, by
    simp (config := {decide := true}) only [storeKey, runBlock_cons, runStep_some,
      runBlock_nil, exec, rr, memOp, State.ea, Reg8.reg, execAlu, readSrc, Option.bind_some, Option.map_some, State.store8,
      BitVec.add_zero, gpr_setReg, gpr_arithFlags,
      mem_setReg, mem_arithFlags, rd_setReg, rd_arithFlags, wr_setReg, wr_arithFlags, writable, ite_true, ite_false]
    rfl, ?_⟩
  constructor
  · rfl
  · constructor
    · intro r hr
      have h9 : r ≠ .edx := by intro h; subst r; exact hr (by decide)
      simp only [gpr_setReg, gpr_arithFlags, h9, ite_false]
    · rfl
    · rfl
    · rfl

theorem descendInput_ok (s : State)
    (readLo : InRegions (s.rd ++ s.wr) (addr32 (s.gpr .edi + (s.gpr .ecx - 1) + 1)) 1)
    (readHi : InRegions (s.rd ++ s.wr) (addr32 (s.gpr .edi + (s.gpr .ecx - 1 + s.gpr .esi))) 1) :
    ∃ s', runBlock isa descendInput s = some s' ∧
      s'.gpr .ecx = s.gpr .ecx - 1 ∧
      s'.gpr .eax = (s.mem (addr32 (s.gpr .edi + (s.gpr .ecx - 1) + 1))).setWidth 32 ^^^
        (s.mem (addr32 (s.gpr .edi + (s.gpr .ecx - 1 + s.gpr .esi)))).setWidth 32 ∧
      Keep [.eax, .ecx, .ebx, .edx] s s' := by
  simp only [addr32] at *
  refine ⟨_, by
    simp (config := {decide := true}) only [descendInput, runBlock_cons, runStep_some,
      runBlock_nil, exec, rr, memOp, State.ea, execAlu, readSrc, Option.bind_some, Option.map_some, State.load8,
      BitVec.add_zero, gpr_setReg, gpr_arithFlags,
      mem_setReg, mem_arithFlags, rd_setReg, rd_arithFlags, wr_setReg, wr_arithFlags, readLo, readHi, ite_true, ite_false]
    rfl, ?_⟩
  refine ⟨?_, ?_, ?_⟩
  · simp only [gpr_setReg, gpr_arithFlags, reduceCtorEq, ite_true, ite_false]
  · simp only [gpr_setReg_self]
  · constructor
    · intro r hr
      have h8 : r ≠ .eax := by intro h; subst r; exact hr (by decide)
      have h23 : r ≠ .ecx := by intro h; subst r; exact hr (by decide)
      have h3 : r ≠ .ebx := by intro h; subst r; exact hr (by decide)
      have h5 : r ≠ .edx := by intro h; subst r; exact hr (by decide)
      have h9 : r ≠ .edx := by intro h; subst r; exact hr (by decide)
      simp only [gpr_setReg, gpr_arithFlags, h8, h23, h3, h5, ite_false]
    · rfl
    · rfl
    · rfl

theorem cmpZero_ok (s : State) :
    ∃ s', runBlock isa [.alu .cmp .ecx (.imm 0)] s = some s' ∧
      zeroFlag s' = some (s.gpr .ecx == 0) ∧ Keep [] s s' := by
  refine ⟨_, by
    simp only [runBlock_cons, exec, execAlu, readSrc, Option.bind_some, runStep_some, runBlock_nil]
    rfl, ?_⟩
  constructor
  · change some ((s.gpr .ecx - 0) == 0) = _
    exact congrArg (fun x : BitVec 32 => some (x == 0)) (by bv_omega)
  · exact ⟨fun _ _ => rfl, rfl, rfl, rfl⟩

end VG.Proof.Rc2.X86
