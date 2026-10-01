import VerifiedGarbage.Proof.Rc2.Arm.Cbc.Loop
import VerifiedGarbage.Proof.Rc2.Arm.KeyIO

/-! # CBC register saves, setup, and restoration -/

namespace VG.Proof.Rc2.Arm.Cbc

open VG VG.Arm VG.Arm.RegUpd VG.Impl.Rc2.Arm

def callerSaved : List Reg := [.r4, .r5, .r6, .r7, .lr]

def savedMem (s : State) : Mem :=
  (((((s.mem.writeW (State.addr (s.gpr .r12) + BitVec.ofNat 64 264) (s.gpr .r4)).writeW (State.addr (s.gpr .r12) + BitVec.ofNat 64 268) (s.gpr .r5)).writeW (State.addr (s.gpr .r12) + BitVec.ofNat 64 272) (s.gpr .r6)).writeW (State.addr (s.gpr .r12) + BitVec.ofNat 64 276) (s.gpr .r7)).writeW (State.addr (s.gpr .r12) + BitVec.ofNat 64 280) (s.gpr .lr))

theorem save_ok (s : State)
    (fit : (s.gpr .r12).toNat + 512 ≤ 2 ^ 32)
    (w0 : InRegions s.wr (State.addr (s.gpr .r12) + BitVec.ofNat 64 264) 4)
    (w1 : InRegions s.wr (State.addr (s.gpr .r12) + BitVec.ofNat 64 268) 4)
    (w2 : InRegions s.wr (State.addr (s.gpr .r12) + BitVec.ofNat 64 272) 4)
    (w3 : InRegions s.wr (State.addr (s.gpr .r12) + BitVec.ofNat 64 276) 4)
    (w4 : InRegions s.wr (State.addr (s.gpr .r12) + BitVec.ofNat 64 280) 4)
    : ∃ s', runBlock isa Impl.Rc2.Arm.Cbc.save s = some s' ∧ Keep [] {s with mem := savedMem s} s' := by
  have a264 : State.addr (s.gpr .r12 + BitVec.ofNat 32 264) = State.addr (s.gpr .r12) + BitVec.ofNat 64 264 := addr_add (by omega)
  have a268 : State.addr (s.gpr .r12 + BitVec.ofNat 32 268) = State.addr (s.gpr .r12) + BitVec.ofNat 64 268 := addr_add (by omega)
  have a272 : State.addr (s.gpr .r12 + BitVec.ofNat 32 272) = State.addr (s.gpr .r12) + BitVec.ofNat 64 272 := addr_add (by omega)
  have a276 : State.addr (s.gpr .r12 + BitVec.ofNat 32 276) = State.addr (s.gpr .r12) + BitVec.ofNat 64 276 := addr_add (by omega)
  have a280 : State.addr (s.gpr .r12 + BitVec.ofNat 32 280) = State.addr (s.gpr .r12) + BitVec.ofNat 64 280 := addr_add (by omega)
  refine ⟨_, by
    simp only [Impl.Rc2.Arm.Cbc.save, runBlock_cons, runStep_some, runBlock_nil,
      exec, Nat.reduceLT, ite_true, State.store32,
      a264, a268, a272, a276, a280, w0, w1, w2, w3, w4]
    rfl, ?_⟩
  exact ⟨fun _ _ => rfl, rfl, rfl, rfl⟩

theorem savedMem_frame (s : State) : Frame [⟨State.addr (s.gpr .r12), 512⟩] s.mem (savedMem s) := by
  unfold savedMem
  apply Frame.writeW (r := ⟨State.addr (s.gpr .r12), 512⟩) (hr := List.mem_cons_self) (hb := Offset.contains_base _ (by decide : 280 + 4 ≤ 512) (by decide))
  apply Frame.writeW (r := ⟨State.addr (s.gpr .r12), 512⟩) (hr := List.mem_cons_self) (hb := Offset.contains_base _ (by decide : 276 + 4 ≤ 512) (by decide))
  apply Frame.writeW (r := ⟨State.addr (s.gpr .r12), 512⟩) (hr := List.mem_cons_self) (hb := Offset.contains_base _ (by decide : 272 + 4 ≤ 512) (by decide))
  apply Frame.writeW (r := ⟨State.addr (s.gpr .r12), 512⟩) (hr := List.mem_cons_self) (hb := Offset.contains_base _ (by decide : 268 + 4 ≤ 512) (by decide))
  apply Frame.writeW (r := ⟨State.addr (s.gpr .r12), 512⟩) (hr := List.mem_cons_self) (hb := Offset.contains_base _ (by decide : 264 + 4 ≤ 512) (by decide))
  exact Frame.refl _ _

theorem savedMem_r4 (s : State) : (savedMem s).readW (State.addr (s.gpr .r12) + BitVec.ofNat 64 264) 32 = s.gpr .r4 := by
  rw [savedMem, Mem.readW_writeW_sep (Offset.sep _ (by decide : 264 + 4 ≤ 280 ∨ 280 + 4 ≤ 264) (by decide) (by decide)) (by decide), Mem.readW_writeW_sep (Offset.sep _ (by decide : 264 + 4 ≤ 276 ∨ 276 + 4 ≤ 264) (by decide) (by decide)) (by decide), Mem.readW_writeW_sep (Offset.sep _ (by decide : 264 + 4 ≤ 272 ∨ 272 + 4 ≤ 264) (by decide) (by decide)) (by decide), Mem.readW_writeW_sep (Offset.sep _ (by decide : 264 + 4 ≤ 268 ∨ 268 + 4 ≤ 264) (by decide) (by decide)) (by decide), Mem.readW_writeW_self32]

theorem savedMem_r5 (s : State) : (savedMem s).readW (State.addr (s.gpr .r12) + BitVec.ofNat 64 268) 32 = s.gpr .r5 := by
  rw [savedMem, Mem.readW_writeW_sep (Offset.sep _ (by decide : 268 + 4 ≤ 280 ∨ 280 + 4 ≤ 268) (by decide) (by decide)) (by decide), Mem.readW_writeW_sep (Offset.sep _ (by decide : 268 + 4 ≤ 276 ∨ 276 + 4 ≤ 268) (by decide) (by decide)) (by decide), Mem.readW_writeW_sep (Offset.sep _ (by decide : 268 + 4 ≤ 272 ∨ 272 + 4 ≤ 268) (by decide) (by decide)) (by decide), Mem.readW_writeW_self32]

theorem savedMem_r6 (s : State) : (savedMem s).readW (State.addr (s.gpr .r12) + BitVec.ofNat 64 272) 32 = s.gpr .r6 := by
  rw [savedMem, Mem.readW_writeW_sep (Offset.sep _ (by decide : 272 + 4 ≤ 280 ∨ 280 + 4 ≤ 272) (by decide) (by decide)) (by decide), Mem.readW_writeW_sep (Offset.sep _ (by decide : 272 + 4 ≤ 276 ∨ 276 + 4 ≤ 272) (by decide) (by decide)) (by decide), Mem.readW_writeW_self32]

theorem savedMem_r7 (s : State) : (savedMem s).readW (State.addr (s.gpr .r12) + BitVec.ofNat 64 276) 32 = s.gpr .r7 := by
  rw [savedMem, Mem.readW_writeW_sep (Offset.sep _ (by decide : 276 + 4 ≤ 280 ∨ 280 + 4 ≤ 276) (by decide) (by decide)) (by decide), Mem.readW_writeW_self32]

theorem savedMem_lr (s : State) : (savedMem s).readW (State.addr (s.gpr .r12) + BitVec.ofNat 64 280) 32 = s.gpr .lr := by
  rw [savedMem, Mem.readW_writeW_self32]

theorem setup_ok (s : State) :
    ∃ s', runBlock isa Impl.Rc2.Arm.Cbc.setup s = some s' ∧
      s'.gpr .r4 = s.gpr .r1 ∧ s'.gpr .r5 = s.gpr .r3 ∧
      s'.gpr .r1 = s.gpr .r2 ∧ s'.gpr .r2 = s.gpr .r12 ∧
      zeroCount s' = some (s.gpr .r3 == 0) ∧ Keep [.r4, .r5, .r1, .r2] s s' := by
  refine ⟨_, by
    simp (config := {decide := true}) only [Impl.Rc2.Arm.Cbc.setup, rr, runBlock_cons,
      runStep_some, runBlock_nil, exec, Op2.eval, Option.map_some, gpr_setReg, ite_true, ite_false]
    rfl, ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [gpr_subFlags, gpr_setReg, reduceCtorEq, ite_true, ite_false]
  · simp only [gpr_subFlags, gpr_setReg, reduceCtorEq, ite_true, ite_false]
  · simp only [gpr_subFlags, gpr_setReg, reduceCtorEq, ite_true, ite_false]
  · simp only [gpr_subFlags, gpr_setReg_self]
  · change some ((s.gpr .r3 - 0) == 0) = _
    exact congrArg (fun x : BitVec 32 => some (x == 0)) (by bv_omega)
  · refine ⟨?_, rfl, rfl, rfl⟩
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [gpr_subFlags, gpr_setReg, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2, ite_false]

theorem restore_ok (s : State) (values : Reg → BitVec 32)
    (fit : (s.gpr .r2).toNat + 512 ≤ 2 ^ 32)
    (r0 : InRegions (s.rd ++ s.wr) (State.addr (s.gpr .r2) + BitVec.ofNat 64 264) 4)
    (v0 : s.mem.readW (State.addr (s.gpr .r2) + BitVec.ofNat 64 264) 32 = values .r4)
    (r1 : InRegions (s.rd ++ s.wr) (State.addr (s.gpr .r2) + BitVec.ofNat 64 268) 4)
    (v1 : s.mem.readW (State.addr (s.gpr .r2) + BitVec.ofNat 64 268) 32 = values .r5)
    (r2 : InRegions (s.rd ++ s.wr) (State.addr (s.gpr .r2) + BitVec.ofNat 64 272) 4)
    (v2 : s.mem.readW (State.addr (s.gpr .r2) + BitVec.ofNat 64 272) 32 = values .r6)
    (r3 : InRegions (s.rd ++ s.wr) (State.addr (s.gpr .r2) + BitVec.ofNat 64 276) 4)
    (v3 : s.mem.readW (State.addr (s.gpr .r2) + BitVec.ofNat 64 276) 32 = values .r7)
    (r4 : InRegions (s.rd ++ s.wr) (State.addr (s.gpr .r2) + BitVec.ofNat 64 280) 4)
    (v4 : s.mem.readW (State.addr (s.gpr .r2) + BitVec.ofNat 64 280) 32 = values .lr)
    : ∃ s', runBlock isa Impl.Rc2.Arm.Cbc.restore s = some s' ∧
      (∀ r ∈ callerSaved, s'.gpr r = values r) ∧ Keep callerSaved s s' := by
  have a264 : State.addr (s.gpr .r2 + BitVec.ofNat 32 264) = State.addr (s.gpr .r2) + BitVec.ofNat 64 264 := addr_add (by omega)
  have a268 : State.addr (s.gpr .r2 + BitVec.ofNat 32 268) = State.addr (s.gpr .r2) + BitVec.ofNat 64 268 := addr_add (by omega)
  have a272 : State.addr (s.gpr .r2 + BitVec.ofNat 32 272) = State.addr (s.gpr .r2) + BitVec.ofNat 64 272 := addr_add (by omega)
  have a276 : State.addr (s.gpr .r2 + BitVec.ofNat 32 276) = State.addr (s.gpr .r2) + BitVec.ofNat 64 276 := addr_add (by omega)
  have a280 : State.addr (s.gpr .r2 + BitVec.ofNat 32 280) = State.addr (s.gpr .r2) + BitVec.ofNat 64 280 := addr_add (by omega)
  refine ⟨_, by
    simp only [Impl.Rc2.Arm.Cbc.restore, runBlock_cons, runStep_some, runBlock_nil,
      exec, Nat.reduceLT, ite_true, State.load32, gpr_setReg, reduceCtorEq, ite_false,
      mem_setReg, rd_setReg, wr_setReg, Option.map_some,
      a264, a268, a272, a276, a280, r0, r1, r2, r3, r4, v0, v1, v2, v3, v4]
    rfl, ?_⟩
  constructor
  · intro r hr
    simp only [callerSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;>
      simp only [gpr_setReg, reduceCtorEq, ite_true, ite_false]
  · refine ⟨?_, rfl, rfl, rfl⟩
    intro r hr
    simp only [callerSaved, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [gpr_setReg, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2, ite_false]

end VG.Proof.Rc2.Arm.Cbc
