import VerifiedGarbage.Proof.TripleDes.Arm.Ecb.Loop

namespace VG.Proof.TripleDes.Arm.Ecb
open VG VG.Arm VG.Arm.RegUpd VG.Impl.TripleDes.Arm
open VG.Proof.Rc2.Arm (Keep gpr_subFlags mem_subFlags rd_subFlags wr_subFlags)

def savedMem (s : State) : Mem :=
  s.mem.writeW (State.addr (s.gpr .r3) + BitVec.ofNat 64 512) (s.gpr .lr)

theorem save_ok (s : State) (fit : (s.gpr .r3).toNat + 1024 ≤ 2 ^ 32)
    (hw : InRegions s.wr (State.addr (s.gpr .r3) + BitVec.ofNat 64 512) 4) :
    ∃ s', runBlock isa Impl.TripleDes.Arm.Ecb.save s = some s' ∧ Keep [] {s with mem := savedMem s} s' := by
  refine ⟨_, by
    simp only [Impl.TripleDes.Arm.Ecb.save, runBlock_cons, runStep_some, runBlock_nil,
      exec, show (512 : Nat) < 4096 from by decide, ite_true, State.store32,
      addr_add (a := s.gpr .r3) (k := 512) (by omega_using [fit]), hw]
    rfl, ?_⟩
  exact ⟨fun _ _ => rfl, rfl, rfl, rfl⟩

theorem savedMem_frame (s : State) : Frame [⟨State.addr (s.gpr .r3), 1024⟩] s.mem (savedMem s) :=
  (Frame.refl _ _).writeW List.mem_cons_self _
    (Offset.contains_base _ (by decide : 512 + 4 ≤ 1024) (by decide))

theorem savedMem_link (s : State) :
    (savedMem s).readW (State.addr (s.gpr .r3) + BitVec.ofNat 64 512) 32 = s.gpr .lr := by
  rw [savedMem, Mem.readW_writeW_self32]

theorem setup_ok (s : State) :
    ∃ s', runBlock isa Impl.TripleDes.Arm.Ecb.setup s = some s' ∧
      s'.gpr .r3 = s.gpr .r2 ∧ s'.gpr .r2 = s.gpr .r3 ∧
      zeroCount s' = some (s.gpr .r2 == 0) ∧ Keep [.r12, .r3, .r2] s s' := by
  refine ⟨_, by
    simp (config := {decide := true}) only [Impl.TripleDes.Arm.Ecb.setup, rr,
      runBlock_cons, runStep_some, runBlock_nil, exec, Op2.eval, ite_true,
      Option.map_some, gpr_setReg, ite_false]
    rfl, ?_, ?_, ?_, ?_⟩
  · simp only [gpr_subFlags, gpr_setReg, reduceCtorEq, ite_false, ite_true]
  · simp only [gpr_subFlags, gpr_setReg, reduceCtorEq, ite_false, ite_true]
  · change some (s.gpr .r2 - 0 == 0) = _
    exact congrArg (fun v : BitVec 32 => some (v == 0)) (by bv_omega)
  · refine ⟨?_, ?_, ?_, ?_⟩
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp only [gpr_subFlags, gpr_setReg, hr.1, hr.2.1, hr.2.2, ite_false]
    · simp only [mem_subFlags, mem_setReg]
    · simp only [rd_subFlags, rd_setReg]
    · simp only [wr_subFlags, wr_setReg]

theorem restore_ok (s : State) (lr : BitVec 32)
    (fit : (s.gpr .r2).toNat + 1024 ≤ 2 ^ 32)
    (hr : InRegions (s.rd ++ s.wr) (State.addr (s.gpr .r2) + BitVec.ofNat 64 512) 4)
    (hv : s.mem.readW (State.addr (s.gpr .r2) + BitVec.ofNat 64 512) 32 = lr) :
    ∃ s', runBlock isa Impl.TripleDes.Arm.Ecb.restore s = some s' ∧
      s'.gpr .lr = lr ∧ Keep [.lr] s s' := by
  refine ⟨_, by
    simp only [Impl.TripleDes.Arm.Ecb.restore, runBlock_cons, runStep_some, runBlock_nil,
      exec, show (512 : Nat) < 4096 from by decide, ite_true, State.load32,
      addr_add (a := s.gpr .r2) (k := 512) (by omega_using [fit]), hr, Option.map_some, hv]
    rfl, gpr_setReg_self _ _ _, ?_⟩
  exact ⟨fun r h => gpr_setReg_of_ne _ _ (by simpa only [List.mem_singleton] using h), rfl, rfl, rfl⟩

theorem LoopPost.scratchRead {d : Spec.TripleDes.Direction} {s s' : State} {n : Nat}
    (h : LoopPost d s n s') (hp : StepPre s n) (i : Nat) (hi : 512 ≤ i ∧ i + 4 ≤ 1024) :
    s'.mem.readW (State.addr (s.gpr .r2) + BitVec.ofNat 64 i) 32 =
      s.mem.readW (State.addr (s.gpr .r2) + BitVec.ofNat 64 i) 32 := by
  have sub : Region.Sub ⟨State.addr (s.gpr .r2) + BitVec.ofNat 64 i, 4⟩ (bufR s) :=
    Offset.sub_base _ hi.2
  have sep : (Region.mk (State.addr (s.gpr .r2) + BitVec.ofNat 64 i) 4).Disjoint
      ⟨State.addr (s.gpr .r2), 512⟩ := Offset.disjoint_base _ (by omega) (by omega)
  apply h.mem.readW (r := ⟨State.addr (s.gpr .r2) + BitVec.ofNat 64 i, 4⟩) (Region.contains_self _ _)
    (hn := by decide)
  simpa only [loopWrites, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] using
    And.intro ((hp.dataBuf.sub_right sub).symm) sep

end VG.Proof.TripleDes.Arm.Ecb
