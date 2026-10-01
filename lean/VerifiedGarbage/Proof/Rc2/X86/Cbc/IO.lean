import VerifiedGarbage.Proof.Rc2.X86.Cbc.Loop
import VerifiedGarbage.Proof.Rc2.X86.KeyIO

/-! CBC register saves, stack arguments, and restoration. -/
namespace VG.Proof.Rc2.X86.Cbc
open VG VG.X86 VG.X86.RegUpd VG.Impl.Rc2.X86

def callerSaved : List Reg := [.ebp, .ebx, .esi, .edi]

def savedMem (s : State) : Mem :=
  ((((s.mem.writeW (addr32 (s.gpr .eax) + BitVec.ofNat 64 264) (s.gpr .ebp)).writeW (addr32 (s.gpr .eax) + BitVec.ofNat 64 268) (s.gpr .ebx)).writeW (addr32 (s.gpr .eax) + BitVec.ofNat 64 272) (s.gpr .esi)).writeW (addr32 (s.gpr .eax) + BitVec.ofNat 64 276) (s.gpr .edi))

theorem save_ok (s : State)
    (fit : (s.gpr .eax).toNat + 512 ≤ 2 ^ 32)
    (w0 : InRegions s.wr (addr32 (s.gpr .eax) + BitVec.ofNat 64 264) 4)
    (w1 : InRegions s.wr (addr32 (s.gpr .eax) + BitVec.ofNat 64 268) 4)
    (w2 : InRegions s.wr (addr32 (s.gpr .eax) + BitVec.ofNat 64 272) 4)
    (w3 : InRegions s.wr (addr32 (s.gpr .eax) + BitVec.ofNat 64 276) 4)
    : ∃ s', runBlock isa Impl.Rc2.X86.Cbc.save s = some s' ∧ Keep [] {s with mem := savedMem s} s' := by
  have a264 : addr32 (s.gpr .eax + BitVec.ofNat 32 264) = addr32 (s.gpr .eax) + BitVec.ofNat 64 264 := addr_add (by omega)
  have a268 : addr32 (s.gpr .eax + BitVec.ofNat 32 268) = addr32 (s.gpr .eax) + BitVec.ofNat 64 268 := addr_add (by omega)
  have a272 : addr32 (s.gpr .eax + BitVec.ofNat 32 272) = addr32 (s.gpr .eax) + BitVec.ofNat 64 272 := addr_add (by omega)
  have a276 : addr32 (s.gpr .eax + BitVec.ofNat 32 276) = addr32 (s.gpr .eax) + BitVec.ofNat 64 276 := addr_add (by omega)
  refine ⟨_, by
    simp only [Impl.Rc2.X86.Cbc.save, runBlock_cons, runStep_some, runBlock_nil,
      exec, memOp, State.ea, State.store32, ← addr_eq_def,
      a264, a268, a272, a276, w0, w1, w2, w3, ite_true]
    rfl, ?_⟩
  exact ⟨fun _ _ => rfl, rfl, rfl, rfl⟩

theorem savedMem_frame (s : State) : Frame [⟨addr32 (s.gpr .eax), 512⟩] s.mem (savedMem s) := by
  unfold savedMem
  apply Frame.writeW (r := ⟨addr32 (s.gpr .eax), 512⟩) (hr := List.mem_cons_self) (hb := Offset.contains_base _ (by decide : 276 + 4 ≤ 512) (by decide))
  apply Frame.writeW (r := ⟨addr32 (s.gpr .eax), 512⟩) (hr := List.mem_cons_self) (hb := Offset.contains_base _ (by decide : 272 + 4 ≤ 512) (by decide))
  apply Frame.writeW (r := ⟨addr32 (s.gpr .eax), 512⟩) (hr := List.mem_cons_self) (hb := Offset.contains_base _ (by decide : 268 + 4 ≤ 512) (by decide))
  apply Frame.writeW (r := ⟨addr32 (s.gpr .eax), 512⟩) (hr := List.mem_cons_self) (hb := Offset.contains_base _ (by decide : 264 + 4 ≤ 512) (by decide))
  exact Frame.refl _ _

theorem savedMem_ebp (s : State) : (savedMem s).readW (addr32 (s.gpr .eax) + BitVec.ofNat 64 264) 32 = s.gpr .ebp := by
  rw [savedMem, Mem.readW_writeW_sep (Offset.sep _ (by decide : 264 + 4 ≤ 276 ∨ 276 + 4 ≤ 264) (by decide) (by decide)) (by decide), Mem.readW_writeW_sep (Offset.sep _ (by decide : 264 + 4 ≤ 272 ∨ 272 + 4 ≤ 264) (by decide) (by decide)) (by decide), Mem.readW_writeW_sep (Offset.sep _ (by decide : 264 + 4 ≤ 268 ∨ 268 + 4 ≤ 264) (by decide) (by decide)) (by decide), Mem.readW_writeW_self32]

theorem savedMem_ebx (s : State) : (savedMem s).readW (addr32 (s.gpr .eax) + BitVec.ofNat 64 268) 32 = s.gpr .ebx := by
  rw [savedMem, Mem.readW_writeW_sep (Offset.sep _ (by decide : 268 + 4 ≤ 276 ∨ 276 + 4 ≤ 268) (by decide) (by decide)) (by decide), Mem.readW_writeW_sep (Offset.sep _ (by decide : 268 + 4 ≤ 272 ∨ 272 + 4 ≤ 268) (by decide) (by decide)) (by decide), Mem.readW_writeW_self32]

theorem savedMem_esi (s : State) : (savedMem s).readW (addr32 (s.gpr .eax) + BitVec.ofNat 64 272) 32 = s.gpr .esi := by
  rw [savedMem, Mem.readW_writeW_sep (Offset.sep _ (by decide : 272 + 4 ≤ 276 ∨ 276 + 4 ≤ 272) (by decide) (by decide)) (by decide), Mem.readW_writeW_self32]

theorem savedMem_edi (s : State) : (savedMem s).readW (addr32 (s.gpr .eax) + BitVec.ofNat 64 276) 32 = s.gpr .edi := by
  rw [savedMem, Mem.readW_writeW_self32]

theorem setup_ok (s : State)
    (readable : ∀ i < 4, InRegions (s.rd ++ s.wr) (argAddr s i) 4) :
    ∃ s', runBlock isa Impl.Rc2.X86.Cbc.setup s = some s' ∧
      s'.gpr .ebx = arg s 0 ∧ s'.gpr .ecx = arg s 1 ∧ s'.gpr .esi = arg s 2 ∧
      s'.gpr .edi = arg s 3 ∧ s'.gpr .ebp = s.gpr .eax ∧
      zeroCount s' = some (arg s 3 == 0) ∧ Keep [.ebp, .ebx, .ecx, .esi, .edi] s s' := by
  have r0 := readable 0 (by decide)
  have r1 := readable 1 (by decide)
  have r2 := readable 2 (by decide)
  have r3 := readable 3 (by decide)
  simp only [argAddr, Nat.mul_zero, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd] at r0 r1 r2 r3
  refine ⟨_, by
    simp (config := {decide := true}) only [Impl.Rc2.X86.Cbc.setup, rr, runBlock_cons, runStep_some,
      runBlock_nil, exec, execAlu, readSrc, memOp, State.ea, State.load32, gpr_setReg,
      mem_setReg, rd_setReg, wr_setReg, r0, r1, r2, r3, ite_true, ite_false, Option.map_some, Option.bind_some]
    rfl, ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [gpr_arithFlags, gpr_setReg, reduceCtorEq, ite_true, ite_false]; rfl
  · simp only [gpr_arithFlags, gpr_setReg, reduceCtorEq, ite_true, ite_false]; rfl
  · simp only [gpr_arithFlags, gpr_setReg, reduceCtorEq, ite_true, ite_false]; rfl
  · simp only [gpr_arithFlags, gpr_setReg, reduceCtorEq, ite_true, ite_false]; rfl
  · simp only [gpr_arithFlags, gpr_setReg, reduceCtorEq, ite_true, ite_false]
  · change some ((arg s 3 - 0) == 0) = _
    exact congrArg (fun x : BitVec 32 => some (x == 0)) (by bv_omega)
  · refine ⟨?_, rfl, rfl, rfl⟩
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [gpr_arithFlags, gpr_setReg, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2, ite_false]

theorem restore_ok (s : State) (values : Reg → BitVec 32)
    (fit : (s.gpr .ebp).toNat + 512 ≤ 2 ^ 32)
    (r0 : InRegions (s.rd ++ s.wr) (addr32 (s.gpr .ebp) + BitVec.ofNat 64 264) 4)
    (v0 : s.mem.readW (addr32 (s.gpr .ebp) + BitVec.ofNat 64 264) 32 = values .ebp)
    (r1 : InRegions (s.rd ++ s.wr) (addr32 (s.gpr .ebp) + BitVec.ofNat 64 268) 4)
    (v1 : s.mem.readW (addr32 (s.gpr .ebp) + BitVec.ofNat 64 268) 32 = values .ebx)
    (r2 : InRegions (s.rd ++ s.wr) (addr32 (s.gpr .ebp) + BitVec.ofNat 64 272) 4)
    (v2 : s.mem.readW (addr32 (s.gpr .ebp) + BitVec.ofNat 64 272) 32 = values .esi)
    (r3 : InRegions (s.rd ++ s.wr) (addr32 (s.gpr .ebp) + BitVec.ofNat 64 276) 4)
    (v3 : s.mem.readW (addr32 (s.gpr .ebp) + BitVec.ofNat 64 276) 32 = values .edi)
    : ∃ s', runBlock isa Impl.Rc2.X86.Cbc.restore s = some s' ∧
      (∀ r ∈ callerSaved, s'.gpr r = values r) ∧ Keep (.eax :: callerSaved) s s' := by
  have a264 : addr32 (s.gpr .ebp + BitVec.ofNat 32 264) = addr32 (s.gpr .ebp) + BitVec.ofNat 64 264 := addr_add (by omega)
  have a268 : addr32 (s.gpr .ebp + BitVec.ofNat 32 268) = addr32 (s.gpr .ebp) + BitVec.ofNat 64 268 := addr_add (by omega)
  have a272 : addr32 (s.gpr .ebp + BitVec.ofNat 32 272) = addr32 (s.gpr .ebp) + BitVec.ofNat 64 272 := addr_add (by omega)
  have a276 : addr32 (s.gpr .ebp + BitVec.ofNat 32 276) = addr32 (s.gpr .ebp) + BitVec.ofNat 64 276 := addr_add (by omega)
  refine ⟨_, by
    simp only [Impl.Rc2.X86.Cbc.restore, rr, runBlock_cons, runStep_some, runBlock_nil,
      exec, readSrc, memOp, State.ea, State.load32, gpr_setReg, reduceCtorEq, ite_false, ite_true,
      mem_setReg, rd_setReg, wr_setReg, Option.map_some, ← addr_eq_def,
      a264, a268, a272, a276, r0, r1, r2, r3, v0, v1, v2, v3]
    rfl, ?_⟩
  constructor
  · intro r hr
    simp only [callerSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;>
      simp only [gpr_setReg, reduceCtorEq, ite_true, ite_false]
  · refine ⟨?_, rfl, rfl, rfl⟩
    intro r hr
    simp only [callerSaved, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [gpr_setReg, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2, ite_false]

end VG.Proof.Rc2.X86.Cbc
