import VerifiedGarbage.Proof.Argon2.AArch64.ReferenceMapLane
import VerifiedGarbage.Proof.Argon2.AArch64.FirstLaneCT
import VerifiedGarbage.Proof.Argon2.AArch64.ReferenceMapWindowCT

/-! Recover the public pass from the frame without exposing the secret word. -/

namespace VG.Proof.Argon2.AArch64.ReferenceMap

open VG VG.AArch64 VG.Impl.Argon2.AArch64.ReferenceMap

def Related (p : Spec.Argon2.Params) (pass lane slice index : Nat) (s t : State) : Prop :=
  Ready p pass lane slice index s ∧ Ready p pass lane slice index t ∧ s.gpr .x19 = t.gpr .x19 ∧ s.sp = t.sp

theorem division_keeps (s : State) (p : Spec.Argon2.Params) (pass lane slice index : Nat)
    (ready : Ready p pass lane slice index s) :
    WP isa VG.Impl.Argon2.AArch64.ReferenceLane.code s fun t =>
      Ready p pass lane slice index t ∧ Divide.Keeps changed s t := by
  refine (ReferenceLane.code_ok s
    (by rw [ready.lanes_nat]; exact ready.bounds.lanesPositive)
    (by rw [ready.lanes_nat]; exact ready.bounds.lanesBound)).mono ?_
  rintro t ⟨_, _, keeps⟩
  have k : Divide.Keeps changed s t := keeps.mono (by decide)
  exact ⟨ready.of_keeps k (keeps.regs .x1 (by decide)), k⟩

theorem division_rel (p : Spec.Argon2.Params) (pass lane slice index : Nat) :
    RelCT isa (Related p pass lane slice index)
      VG.Impl.Argon2.AArch64.ReferenceLane.code (Related p pass lane slice index) := by
  have full := (ReferenceLane.code_secret_rel.mono
    (P' := Related p pass lane slice index) (fun _ _ hp => hp.2.2.2)
    (fun _ _ h => h)).wpDep (fun s t hp =>
      ⟨division_keeps s p pass lane slice index hp.1,
        division_keeps t p pass lane slice index hp.2.1⟩)
  refine full.mono (fun _ _ h => h) ?_
  intro a b h
  obtain ⟨eq, s, t, hp, ha, hb⟩ := h
  exact ⟨ha.1, hb.1, (ha.2.regs .x19 (by decide)).trans
    (hp.2.2.1.trans (hb.2.regs .x19 (by decide)).symm), eq⟩

theorem loadPass_rel : RelCT isa (fun s t => s.gpr .x19 = t.gpr .x19 ∧ s.sp = t.sp)
    (.block loadPass) (fun s t => s.sp = t.sp) :=
  (RelCT.taintRegs (τ := Taint.ofRegs [.x19])
    (fun _ _ h => ⟨h.2, by
      intro r hr
      simp only [Taint.mem_ofRegs, List.mem_singleton] at hr
      subst r
      exact h.1⟩) [] (by taint_decide)).mono
    (fun _ _ h => h) (fun _ _ h => h.1)

def Loaded (p : Spec.Argon2.Params) (pass lane slice index : Nat) (s t : State) : Prop :=
  Related p pass lane slice index s t ∧
    s.gpr .x5 = BitVec.ofNat 64 pass ∧ t.gpr .x5 = BitVec.ofNat 64 pass

theorem loadPass_public (s : State) (p : Spec.Argon2.Params) (pass lane slice index : Nat)
    (ready : Ready p pass lane slice index s) : WP isa (.block loadPass) s fun t =>
      Ready p pass lane slice index t ∧ t.gpr .x5 = BitVec.ofNat 64 pass ∧
        Divide.Keeps changed s t := by
  refine (loadPass_ok s ready.passRead).mono ?_
  rintro t ⟨loaded, keeps⟩
  have k : Divide.Keeps changed s t := keeps.mono (by decide)
  exact ⟨ready.of_keeps k (keeps.regs .x1 (by decide)), loaded.trans ready.passWord, k⟩

theorem loadPass_public_rel (p : Spec.Argon2.Params) (pass lane slice index : Nat) :
    RelCT isa (Related p pass lane slice index) (.block loadPass)
      (Loaded p pass lane slice index) := by
  have full := (loadPass_rel.mono (P' := Related p pass lane slice index)
    (fun _ _ h => h.2.2) (fun _ _ h => h)).wpDep (fun s t hp =>
      ⟨loadPass_public s p pass lane slice index hp.1,
        loadPass_public t p pass lane slice index hp.2.1⟩)
  refine full.mono (fun _ _ h => h) ?_
  intro a b h
  obtain ⟨eq, s, t, hp, ha, hb⟩ := h
  exact ⟨⟨ha.1, hb.1, (ha.2.2.regs .x19 (by decide)).trans
    (hp.2.2.1.trans (hb.2.2.regs .x19 (by decide)).symm), eq⟩, ha.2.1, hb.2.1⟩

theorem firstLane_loaded_rel (p : Spec.Argon2.Params) (pass lane slice index : Nat) :
    RelCT isa (Loaded p pass lane slice index) VG.Impl.Argon2.AArch64.FirstLane.code
      (Loaded p pass lane slice index) := by
  have trace := FirstLane.code_rel.mono (P' := Loaded p pass lane slice index)
    (fun _ _ hp => ⟨hp.1.2.2.2, by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hp.2.1.trans hp.2.2.symm
      · exact hp.1.1.position.slice.trans hp.1.2.1.position.slice.symm⟩) (fun _ _ h => h)
  have full := trace.wpDep (fun s t _ => ⟨FirstLane.code_ok s, FirstLane.code_ok t⟩)
  refine full.mono (fun _ _ h => h) ?_
  intro a b h
  obtain ⟨eq, s, t, hp, ha, hb⟩ := h
  have ka : Divide.Keeps changed s a := ha.2.mono (by decide)
  have kb : Divide.Keeps changed t b := hb.2.mono (by decide)
  refine ⟨⟨hp.1.1.of_keeps ka (ha.2.regs .x1 (by decide)),
    hp.1.2.1.of_keeps kb (hb.2.regs .x1 (by decide)),
    (ka.regs .x19 (by decide)).trans (hp.1.2.2.1.trans (kb.regs .x19 (by decide)).symm), eq.1⟩, ?_, ?_⟩
  · exact (ha.2.regs .x5 (by decide)).trans hp.2.1
  · exact (hb.2.regs .x5 (by decide)).trans hp.2.2

theorem laneArgs_secret_rel : RelCT isa (fun s t => s.sp = t.sp) (.block laneArgs)
    (fun s t => s.sp = t.sp) :=
  (RelCT.taintRegs (τ := Taint.ofRegs [])
    (fun _ _ h => ⟨h, by simp [Taint.mem_ofRegs]⟩) [] (by taint_decide)).mono
    (fun _ _ h => h) (fun _ _ h => h.1)

theorem prepareLanes_rel (p : Spec.Argon2.Params) (pass lane slice index : Nat) :
    RelCT isa (Related p pass lane slice index) prepareLanes PublicPosition := by
  have head := (division_rel p pass lane slice index).seq
    ((loadPass_public_rel p pass lane slice index).seq (firstLane_loaded_rel p pass lane slice index))
  have trace := head.seq (laneArgs_secret_rel.mono (fun _ _ hp => hp.1.2.2.2) (fun _ _ h => h))
  have full := trace.wpDep (fun s t hp =>
    ⟨prepareLanes_ok s p pass lane slice index hp.1,
      prepareLanes_ok t p pass lane slice index hp.2.1⟩)
  refine full.mono (fun _ _ h => h) ?_
  intro a b h
  obtain ⟨eq, _, _, _, ha, hb⟩ := h
  refine ⟨eq, ?_⟩
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · apply BitVec.eq_of_toNat_eq
    exact ha.pass.trans hb.pass.symm
  · exact ha.position.slice.trans hb.position.slice.symm
  · exact ha.position.segmentLength.trans hb.position.segmentLength.symm

end VG.Proof.Argon2.AArch64.ReferenceMap
