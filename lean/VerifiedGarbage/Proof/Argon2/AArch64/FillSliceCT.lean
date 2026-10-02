import VerifiedGarbage.Proof.Argon2.AArch64.FillSlice
import VerifiedGarbage.Proof.Argon2.AArch64.FillLanesCT

/-! A complete slice exposes only its specified reference log. -/

namespace VG.Proof.Argon2.AArch64.FillSlice

open VG VG.AArch64 VG.Spec.Argon2

structure Related (p : Params) (pass slice : Nat) (leftState rightState : FillState) (s t : State) : Prop where
  left : Ready p pass slice s
  right : Ready p pass slice t
  bases : s.gpr .x19 = t.gpr .x19
  stacks : s.sp = t.sp
  matrices : FillKernel.matrix s = FillKernel.matrix t
  work : AddressCalls.work s = AddressCalls.work t
  leftMatrix : Proof.Argon2.Represents s.mem (FillKernel.matrix s) p.blocks leftState.memory
  rightMatrix : Proof.Argon2.Represents t.mem (FillKernel.matrix t) p.blocks rightState.memory
  indices : (Proof.Argon2.lanes p pass slice 0 p.lanes leftState).indices =
    (Proof.Argon2.lanes p pass slice 0 p.lanes rightState).indices

theorem setup_trace : RelCT isa (fun s t : State => s.sp = t.sp) (.block Impl.Argon2.AArch64.FillSlice.setup) (fun _ _ => True) :=
  (RelCT.taintRegs (τ := Taint.ofRegs [])
    (fun _ _ h => ⟨h, by intro r hr; simp only [Taint.mem_ofRegs, List.not_mem_nil] at hr⟩)
    [] (by taint_decide)).mono (fun _ _ h => h) (fun _ _ _ => trivial)

theorem setup_public_rel (p : Params) (pass slice : Nat) (leftState rightState : FillState) :
    RelCT isa (Related p pass slice leftState rightState) (.block Impl.Argon2.AArch64.FillSlice.setup)
      (FillLanes.Related p pass 0 slice p.lanes leftState rightState) := by
  have trace := setup_trace.mono (P' := Related p pass slice leftState rightState)
    (fun _ _ h => h.stacks) (fun _ _ h => h)
  have full := trace.wpDep (fun s t h => ⟨setup_ok s p pass slice h.left, setup_ok t p pass slice h.right⟩)
  refine full.mono (fun _ _ h => h) ?_
  intro a b h
  obtain ⟨_, s, t, hp, ha, hb⟩ := h
  refine ⟨⟨ha.ready, hb.ready, ?_, ?_, ?_, ?_⟩, ?_, ?_, hp.indices⟩
  · rw [ha.keeps.regs .x19 (by decide), hb.keeps.regs .x19 (by decide)]; exact hp.bases
  · rw [ha.keeps.sp, hb.keeps.sp]; exact hp.stacks
  · unfold FillKernel.matrix
    rw [ha.keeps.mem, hb.keeps.mem, ha.keeps.regs .x19 (by decide), hb.keeps.regs .x19 (by decide)]
    exact hp.matrices
  · unfold AddressCalls.work
    rw [ha.keeps.mem, hb.keeps.mem, ha.keeps.regs .x19 (by decide), hb.keeps.regs .x19 (by decide)]
    exact hp.work
  · unfold FillKernel.matrix; rw [ha.keeps.mem, ha.keeps.regs .x19 (by decide)]; exact hp.leftMatrix
  · unfold FillKernel.matrix; rw [hb.keeps.mem, hb.keeps.regs .x19 (by decide)]; exact hp.rightMatrix

theorem code_rel (p : Params) (pass slice : Nat) (leftState rightState : FillState) :
    RelCT isa (Related p pass slice leftState rightState) Impl.Argon2.AArch64.FillSlice.code (fun _ _ => True) := by
  intro s t ts tt a b hp ea eb
  cases ea with
  | seq setupA lanesA =>
    cases eb with
    | seq setupB lanesB =>
      obtain ⟨setupTrace, related⟩ := setup_public_rel p pass slice leftState rightState _ _ _ _ _ _ hp setupA setupB
      obtain ⟨lanesTrace, _⟩ := FillLanes.loop_rel p pass 0 slice p.lanes leftState rightState
        hp.left.parameters.lanesPositive (by omega) _ _ _ _ _ _ related lanesA lanesB
      exact ⟨by rw [setupTrace, lanesTrace], trivial⟩

end VG.Proof.Argon2.AArch64.FillSlice
