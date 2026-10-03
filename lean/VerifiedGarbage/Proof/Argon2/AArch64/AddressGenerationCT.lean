import VerifiedGarbage.Proof.Argon2.AArch64.AddressCallsCT
import VerifiedGarbage.Proof.Argon2.AArch64.AddressCallsPrepare
import VerifiedGarbage.Proof.Argon2.AArch64.AddressInputCT

/-! Independent-address generation keeps its entire trace independent of secrets. -/

namespace VG.Proof.Argon2.AArch64.AddressCalls

open VG VG.AArch64 VG.Impl.Argon2.AArch64.AddressCalls

theorem Related.of_stable {s t a b : State} (h : Related s t)
    (ha : Stable s a) (hb : Stable t b) : Related a b :=
  ⟨ha.ready, hb.ready,
    (ha.regs .x19 (by simp [FillCompress.loopRegs])).trans
      (h.bases.trans (hb.regs .x19 (by simp [FillCompress.loopRegs])).symm),
    ha.sp.trans (h.stacks.trans hb.sp.symm),
    ha.work_eq.trans (h.work.trans hb.work_eq.symm)⟩

theorem input_pointer_rel : RelCT isa (fun s t => s.gpr .x19 = t.gpr .x19 ∧ s.sp = t.sp)
    (.block (pointer 5120)) (fun s t => s.sp = t.sp) :=
  (RelCT.taintRegs (τ := Taint.ofRegs [.x19])
    (fun _ _ h => ⟨h.2, by
      intro r hr
      simp only [Taint.mem_ofRegs, List.mem_singleton] at hr
      subst r
      exact h.1⟩) [] (by taint_decide)).mono
    (fun _ _ h => h) (fun _ _ h => h.1)

theorem zero_pointer_rel : RelCT isa (fun s t => s.gpr .x19 = t.gpr .x19 ∧ s.sp = t.sp)
    (.block (pointer 7168)) (fun s t => s.sp = t.sp) :=
  (RelCT.taintRegs (τ := Taint.ofRegs [.x19])
    (fun _ _ h => ⟨h.2, by
      intro r hr
      simp only [Taint.mem_ofRegs, List.mem_singleton] at hr
      subst r
      exact h.1⟩) [] (by taint_decide)).mono
    (fun _ _ h => h) (fun _ _ h => h.1)

structure PointRelated (s t : State) : Prop where
  related : Related s t
  pointer : s.gpr .x0 = t.gpr .x0

theorem pointer_public_rel (offset : Nat) (bound : offset ≤ 8192)
    (trace : RelCT isa (fun s t => s.gpr .x19 = t.gpr .x19 ∧ s.sp = t.sp)
      (.block (pointer offset)) (fun s t => s.sp = t.sp)) :
    RelCT isa Related (.block (pointer offset)) PointRelated := by
  have publicTrace := trace.mono (P' := Related) (fun _ _ h => ⟨h.bases, h.stacks⟩) (fun _ _ h => h)
  have full := publicTrace.wpDep (fun s t h =>
    ⟨pointer_ok s offset bound h.left.frameRead, pointer_ok t offset bound h.right.frameRead⟩)
  refine full.mono (fun _ _ h => h) ?_
  intro a b h
  obtain ⟨_, s, t, hp, ⟨pa, ka⟩, ⟨pb, kb⟩⟩ := h
  exact ⟨hp.of_stable (pointer_stable hp.left ka) (pointer_stable hp.right kb),
    pa.trans ((congrArg (· + BitVec.ofNat 64 offset) hp.work).trans pb.symm)⟩

theorem clearAt_rel (offset : Nat) (bound : offset + 1024 ≤ 8192)
    (trace : RelCT isa (fun s t => s.gpr .x19 = t.gpr .x19 ∧ s.sp = t.sp)
      (.block (pointer offset)) (fun s t => s.sp = t.sp)) :
    RelCT isa Related (clearAt offset) Related := by
  have clear := ClearBlock.code_rel.mono (P' := PointRelated)
    (fun _ _ h => ⟨h.related.stacks, h.pointer⟩) (fun _ _ h => h)
  have blocks := (pointer_public_rel offset (by omega) trace).seq clear
  have full := blocks.wpDep (fun s t h =>
    ⟨clearAt_ok s h.left offset bound, clearAt_ok t h.right offset bound⟩)
  refine full.mono (fun _ _ h => h) ?_
  intro a b h
  obtain ⟨_, s, t, hp, ha, hb⟩ := h
  exact hp.of_stable (ha.stable bound) (hb.stable bound)

structure PrepareRelated (s t : State) : Prop where
  related : Related s t
  leftReads : ∀ d ∈ [0, 8, 72, 112, 240], InRegions (s.rd ++ s.wr) (off (s.gpr .x19) d) 8
  rightReads : ∀ d ∈ [0, 8, 72, 112, 240], InRegions (t.rd ++ t.wr) (off (t.gpr .x19) d) 8

theorem prepare_rel : RelCT isa PrepareRelated prepare Related := by
  have header := AddressHeader.code_rel.mono (P' := PointRelated) (by
    intro s t h
    refine ⟨h.related.stacks, ?_⟩
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact h.pointer
    · exact h.related.bases) (fun _ _ h => h)
  have trace := (clearAt_rel 5120 (by decide) input_pointer_rel).seq
    ((clearAt_rel 7168 (by decide) zero_pointer_rel).seq
      ((pointer_public_rel 5120 (by decide) input_pointer_rel).seq header))
  have narrowed := trace.mono (P' := PrepareRelated) (fun _ _ h => h.related) (fun _ _ h => h)
  have full := narrowed.wpDep (fun s t h =>
    ⟨prepare_layout_ok s h.related.left h.leftReads,
      prepare_layout_ok t h.related.right h.rightReads⟩)
  refine full.mono (fun _ _ h => h) ?_
  intro a b h
  obtain ⟨_, s, t, hp, ha, hb⟩ := h
  exact hp.related.of_stable ha.stable hb.stable

theorem code_rel : RelCT isa PrepareRelated code Related := prepare_rel.seq calls_rel

end VG.Proof.Argon2.AArch64.AddressCalls
