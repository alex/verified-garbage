import VerifiedGarbage.Proof.Argon2.X86_64.FillKernelPrepare
import VerifiedGarbage.Proof.Argon2.X86_64.ReferenceMapCT
import VerifiedGarbage.Proof.Argon2.X86_64.FillPointersCT

/-! Reference mapping exposes no more than the permitted reference coordinates. -/

namespace VG.Proof.Argon2.X86_64.FillKernel

open VG VG.X86_64 VG.Spec.Argon2

structure Related (p : Params) (pass lane slice index : Nat) (s t : State) : Prop where
  left : Ready p pass lane slice index s
  right : Ready p pass lane slice index t
  bases : s.gpr .rbp = t.gpr .rbp
  stacks : s.gpr .rsp = t.gpr .rsp
  matrices : matrix s = matrix t
  scratch : work s = work t
  references : Spec.Argon2.reference p pass lane slice index (s.gpr .rdi) =
    Spec.Argon2.reference p pass lane slice index (t.gpr .rdi)

structure PointerRelated (p : Params) (lane slice index : Nat) (s t : State) : Prop where
  left : Layout p s
  right : Layout p t
  leftPosition : ReferenceMap.Position p lane slice index s
  rightPosition : ReferenceMap.Position p lane slice index t
  bases : s.gpr .rbp = t.gpr .rbp
  matrices : matrix s = matrix t

theorem lanes_rel : RelCT isa (fun s t => s.gpr .rbp = t.gpr .rbp)
    (.block Impl.Argon2.X86_64.FillKernel.lanes) (fun _ _ => True) :=
  RelCT.taint (A := taint) (Taint.ofRegs [.rbp])
    (fun _ _ h => Taint.agree_ofRegs (by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      subst r
      exact h)) (by taint_decide)

theorem lanes_ready (s : State) (p : Params) (pass lane slice index : Nat)
    (h : Ready p pass lane slice index s) :
    WP isa (.block Impl.Argon2.X86_64.FillKernel.lanes) s fun t =>
      ReferenceMap.Ready p pass lane slice index t ∧ Divide.Keeps ReferenceMap.changed s t := by
  refine (load_ok s .rsi 184 (h.layout.frameRead 184 (by simp))).mono ?_
  rintro t ⟨lanes, keeps⟩
  have k : Divide.Keeps ReferenceMap.changed s t := keeps.mono (by decide)
  refine ⟨⟨h.bounds, h.position.of_keeps k, lanes.trans h.lanesWord, ?_, ?_⟩, k⟩
  · rw [k.rd, k.wr, k.regs .rbp (by decide)]
    simpa only [off, show BitVec.ofNat 64 0 = 0#64 from rfl, BitVec.add_zero]
      using h.layout.frameRead 0 (by simp)
  · rw [k.mem, k.regs .rbp (by decide)]
    simpa only [off, show BitVec.ofNat 64 0 = 0#64 from rfl, BitVec.add_zero] using h.passWord

theorem lanes_public_rel (p : Params) (pass lane slice index : Nat) :
    RelCT isa (Related p pass lane slice index) (.block Impl.Argon2.X86_64.FillKernel.lanes)
      (ReferenceMap.Related p pass lane slice index) := by
  have trace := lanes_rel.mono (P' := Related p pass lane slice index)
    (fun _ _ h => h.bases) (fun _ _ h => h)
  have full := trace.wpDep (fun s t h =>
    ⟨lanes_ready s p pass lane slice index h.left, lanes_ready t p pass lane slice index h.right⟩)
  refine full.mono (fun _ _ h => h) ?_
  intro a b h
  obtain ⟨_, s, t, hp, ha, hb⟩ := h
  exact ⟨ha.1, hb.1, (ha.2.regs .rbp (by decide)).trans
    (hp.bases.trans (hb.2.regs .rbp (by decide)).symm)⟩

theorem mapping_public_rel (p : Params) (pass lane slice index : Nat) :
    RelCT isa (Related p pass lane slice index) Impl.Argon2.X86_64.FillKernel.mapping
      (PointerRelated p lane slice index) := by
  have trace := (lanes_public_rel p pass lane slice index).seq (ReferenceMap.code_rel p pass lane slice index)
  have full := trace.wpDep (fun s t h =>
    ⟨mapping_ok s p pass lane slice index h.left, mapping_ok t p pass lane slice index h.right⟩)
  refine full.mono (fun _ _ h => h) ?_
  intro a b h
  obtain ⟨_, s, t, hp, ha, hb⟩ := h
  refine ⟨hp.left.layout.of_keeps ha.keeps, hp.right.layout.of_keeps hb.keeps,
    hp.left.position.of_keeps ha.keeps, hp.right.position.of_keeps hb.keeps, ?_, ?_⟩
  · exact (ha.keeps.regs .rbp (by decide)).trans (hp.bases.trans (hb.keeps.regs .rbp (by decide)).symm)
  · unfold matrix
    rw [ha.keeps.mem, hb.keeps.mem, ha.keeps.regs .rbp (by decide), hb.keeps.regs .rbp (by decide)]
    exact hp.matrices

theorem matrix_rel : RelCT isa (fun s t => s.gpr .rbp = t.gpr .rbp)
    (.block Impl.Argon2.X86_64.FillKernel.matrix) (fun _ _ => True) :=
  RelCT.taint (A := taint) (Taint.ofRegs [.rbp])
    (fun _ _ h => Taint.agree_ofRegs (by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      subst r
      exact h)) (by taint_decide)

theorem pointers_trace (p : Params) (lane slice index : Nat) :
    RelCT isa (PointerRelated p lane slice index) Impl.Argon2.X86_64.FillKernel.pointers
      (fun _ _ => True) := by
  have trace := matrix_rel.mono (P' := PointerRelated p lane slice index)
    (fun _ _ h => h.bases) (fun _ _ h => h)
  have full := trace.wpDep (fun s t h =>
    ⟨load_ok s .r8 232 (h.left.frameRead 232 (by simp)),
      load_ok t .r8 232 (h.right.frameRead 232 (by simp))⟩)
  have args : RelCT isa (PointerRelated p lane slice index) (.block Impl.Argon2.X86_64.FillKernel.matrix)
      (fun s t => ∀ r ∈ [Reg.r8, .rbx, .r12, .r13, .r14, .r15], s.gpr r = t.gpr r) :=
    full.mono (fun _ _ h => h) (by
      intro a b h r hr
      obtain ⟨_, s, t, hp, ⟨va, ka⟩, ⟨vb, kb⟩⟩ := h
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
      · exact va.trans (hp.matrices.trans vb.symm)
      all_goals rw [ka.regs _ (by decide), kb.regs _ (by decide)]
      · exact hp.leftPosition.current.trans hp.rightPosition.current.symm
      · exact hp.leftPosition.laneLength.trans hp.rightPosition.laneLength.symm
      · exact hp.leftPosition.segmentLength.trans hp.rightPosition.segmentLength.symm
      · exact hp.leftPosition.slice.trans hp.rightPosition.slice.symm
      · exact hp.leftPosition.index.trans hp.rightPosition.index.symm)
  exact (args.seq FillPointers.code_rel).mono (fun _ _ h => h) (fun _ _ _ => trivial)

end VG.Proof.Argon2.X86_64.FillKernel
