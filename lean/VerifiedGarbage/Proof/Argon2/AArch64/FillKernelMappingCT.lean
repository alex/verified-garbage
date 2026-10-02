import VerifiedGarbage.Proof.Argon2.AArch64.FillKernelPrepare
import VerifiedGarbage.Proof.Argon2.AArch64.ReferenceMapCT
import VerifiedGarbage.Proof.Argon2.AArch64.FillPointersCT

/-! Reference mapping exposes no more than the permitted reference coordinates. -/

namespace VG.Proof.Argon2.AArch64.FillKernel

open VG VG.AArch64 VG.Spec.Argon2

structure Related (p : Params) (pass lane slice index : Nat) (s t : State) : Prop where
  left : Ready p pass lane slice index s
  right : Ready p pass lane slice index t
  bases : s.gpr .x19 = t.gpr .x19
  stacks : s.sp = t.sp
  matrices : matrix s = matrix t
  scratch : work s = work t
  references : Spec.Argon2.reference p pass lane slice index (s.gpr .x0) =
    Spec.Argon2.reference p pass lane slice index (t.gpr .x0)

structure PointerRelated (p : Params) (lane slice index : Nat) (s t : State) : Prop where
  left : Layout p s
  right : Layout p t
  leftPosition : ReferenceMap.Position p lane slice index s
  rightPosition : ReferenceMap.Position p lane slice index t
  bases : s.gpr .x19 = t.gpr .x19
  matrices : matrix s = matrix t
  stacks : s.sp = t.sp

theorem lanes_rel : RelCT isa (fun s t => s.gpr .x19 = t.gpr .x19 ∧ s.sp = t.sp)
    (.block Impl.Argon2.AArch64.FillKernel.lanes) (fun s t => s.sp = t.sp) :=
  (RelCT.taintRegs (τ := Taint.ofRegs [.x19])
    (fun _ _ h => ⟨h.2, by
      intro r hr
      simp only [Taint.mem_ofRegs, List.mem_singleton] at hr
      subst r
      exact h.1⟩) [] (by taint_decide)).mono
    (fun _ _ h => h) (fun _ _ h => h.1)

theorem lanes_ready (s : State) (p : Params) (pass lane slice index : Nat)
    (h : Ready p pass lane slice index s) :
    WP isa (.block Impl.Argon2.AArch64.FillKernel.lanes) s fun t =>
      ReferenceMap.Ready p pass lane slice index t ∧ Divide.Keeps ReferenceMap.changed s t := by
  refine (load_ok s .x1 184 (by decide) (by decide) (h.layout.frameRead 184 (by simp))).mono ?_
  rintro t ⟨lanes, keeps⟩
  have k : Divide.Keeps ReferenceMap.changed s t := keeps.mono (by decide)
  refine ⟨⟨h.bounds, h.position.of_keeps k, lanes.trans h.lanesWord, ?_, ?_⟩, k⟩
  · rw [k.rd, k.wr, k.regs .x19 (by decide)]
    simpa only [off, show BitVec.ofNat 64 0 = 0#64 from rfl, BitVec.add_zero]
      using h.layout.frameRead 0 (by simp)
  · rw [k.mem, k.regs .x19 (by decide)]
    simpa only [off, show BitVec.ofNat 64 0 = 0#64 from rfl, BitVec.add_zero] using h.passWord

theorem lanes_public_rel (p : Params) (pass lane slice index : Nat) :
    RelCT isa (Related p pass lane slice index) (.block Impl.Argon2.AArch64.FillKernel.lanes)
      (ReferenceMap.Related p pass lane slice index) := by
  have trace := lanes_rel.mono (P' := Related p pass lane slice index)
    (fun _ _ h => ⟨h.bases, h.stacks⟩) (fun _ _ h => h)
  have full := trace.wpDep (fun s t h =>
    ⟨lanes_ready s p pass lane slice index h.left, lanes_ready t p pass lane slice index h.right⟩)
  refine full.mono (fun _ _ h => h) ?_
  intro a b h
  obtain ⟨eq, s, t, hp, ha, hb⟩ := h
  exact ⟨ha.1, hb.1, (ha.2.regs .x19 (by decide)).trans
    (hp.bases.trans (hb.2.regs .x19 (by decide)).symm), eq⟩

theorem mapping_public_rel (p : Params) (pass lane slice index : Nat) :
    RelCT isa (Related p pass lane slice index) Impl.Argon2.AArch64.FillKernel.mapping
      (PointerRelated p lane slice index) := by
  have trace := (lanes_public_rel p pass lane slice index).seq (ReferenceMap.code_rel p pass lane slice index)
  have full := trace.wpDep (fun s t h =>
    ⟨mapping_ok s p pass lane slice index h.left, mapping_ok t p pass lane slice index h.right⟩)
  refine full.mono (fun _ _ h => h) ?_
  intro a b h
  obtain ⟨eq, s, t, hp, ha, hb⟩ := h
  refine ⟨hp.left.layout.of_keeps ha.keeps, hp.right.layout.of_keeps hb.keeps,
    hp.left.position.of_keeps ha.keeps, hp.right.position.of_keeps hb.keeps, ?_, ?_, eq⟩
  · exact (ha.keeps.regs .x19 (by decide)).trans (hp.bases.trans (hb.keeps.regs .x19 (by decide)).symm)
  · unfold matrix
    rw [ha.keeps.mem, hb.keeps.mem, ha.keeps.regs .x19 (by decide), hb.keeps.regs .x19 (by decide)]
    exact hp.matrices

theorem matrix_rel : RelCT isa (fun s t => s.gpr .x19 = t.gpr .x19 ∧ s.sp = t.sp)
    (.block Impl.Argon2.AArch64.FillKernel.matrix) (fun s t => s.sp = t.sp) :=
  (RelCT.taintRegs (τ := Taint.ofRegs [.x19])
    (fun _ _ h => ⟨h.2, by
      intro r hr
      simp only [Taint.mem_ofRegs, List.mem_singleton] at hr
      subst r
      exact h.1⟩) [] (by taint_decide)).mono
    (fun _ _ h => h) (fun _ _ h => h.1)

theorem pointers_trace (p : Params) (lane slice index : Nat) :
    RelCT isa (PointerRelated p lane slice index) Impl.Argon2.AArch64.FillKernel.pointers
      (fun s t => s.sp = t.sp) := by
  have trace := matrix_rel.mono (P' := PointerRelated p lane slice index)
    (fun _ _ h => ⟨h.bases, h.stacks⟩) (fun _ _ h => h)
  have full := trace.wpDep (fun s t h =>
    ⟨load_ok s .x4 232 (by decide) (by decide) (h.left.frameRead 232 (by simp)),
      load_ok t .x4 232 (by decide) (by decide) (h.right.frameRead 232 (by simp))⟩)
  have args : RelCT isa (PointerRelated p lane slice index) (.block Impl.Argon2.AArch64.FillKernel.matrix)
      (fun s t => s.sp = t.sp ∧ ∀ r ∈ [Reg.x4, .x24, .x20, .x21, .x22, .x23], s.gpr r = t.gpr r) :=
    full.mono (fun _ _ h => h) (by
      intro a b h
      obtain ⟨eq, s, t, hp, ⟨va, ka⟩, ⟨vb, kb⟩⟩ := h
      refine ⟨eq, ?_⟩
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
      · exact va.trans (hp.matrices.trans vb.symm)
      all_goals rw [ka.regs _ (by decide), kb.regs _ (by decide)]
      · exact hp.leftPosition.current.trans hp.rightPosition.current.symm
      · exact hp.leftPosition.laneLength.trans hp.rightPosition.laneLength.symm
      · exact hp.leftPosition.segmentLength.trans hp.rightPosition.segmentLength.symm
      · exact hp.leftPosition.slice.trans hp.rightPosition.slice.symm
      · exact hp.leftPosition.index.trans hp.rightPosition.index.symm)
  exact (args.seq FillPointers.code_rel).mono (fun _ _ h => h) (fun _ _ h => h.1)

end VG.Proof.Argon2.AArch64.FillKernel
