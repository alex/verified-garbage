import VerifiedGarbage.Proof.Argon2.AArch64.InitialCTState

/-! H₀ finalization and its fixed-size digest copy reveal no input contents. -/

namespace VG.Proof.Argon2.AArch64.Initial

open VG VG.AArch64 VG.Impl.Argon2.AArch64.Initial

theorem finishCount_rel : RelCT isa (RelatedRegs [.x20]) (.block ([Impl.Argon2.AArch64.Instructions.mov .x1 .x20].flatten))
    (fun s t => RelatedRegs [.x20] s t ∧ s.gpr .x1 = t.gpr .x1) := by
  have ct := (RelCT.taint (A := taint) (P := RelatedRegs [.x20]) (Taint.ofRegs [])
    (fun _ _ hp => ⟨hp.1.sp, by simp [Taint.ofRegs]⟩)
    (c := .block ([Impl.Argon2.AArch64.Instructions.mov .x1 .x20].flatten)) (by taint_decide)).wpDep
    (fun s t _ => ⟨finishCount_ok s, finishCount_ok t⟩)
  apply ct.mono (fun _ _ h => h)
  rintro a b ⟨_, s, t, hp, ⟨ca, _, ka⟩, ⟨cb, _, kb⟩⟩
  refine ⟨⟨hp.1.keeps (Keeps.of_hash ka) (Keeps.of_hash kb), ?_⟩, ?_⟩
  · intro r hr
    simp only [List.mem_singleton] at hr; subst r
    rw [ka.regs .x20 (by decide) (by decide), kb.regs .x20 (by decide) (by decide)]
    exact hp.2 _ (by simp)
  · rw [ca, cb]; exact hp.2 _ (by simp)

theorem finalize_hash_rel (v : HPrime.Backend) :
    RelCT isa (fun s t => RelatedRegs [.x20] s t ∧ s.gpr .x1 = t.gpr .x1)
      (Impl.Argon2.AArch64.HPrime.finalize v.hash) Related := by
  have ct := HPrime.finalize_rel v (P := fun s t => RelatedRegs [.x20] s t ∧ s.gpr .x1 = t.gpr .x1)
    (fun s t h => ⟨finalize_ready h.1.1.left, finalize_ready h.1.1.right, h.1.1.bx, h.2, h.1.1.sp⟩)
  have result := hash_keeps_rel [] (by simp) ct (fun _ _ h => ⟨h.1.1, by simp⟩)
    (fun s t h => ⟨HPrime.finalize_keeps v s (finalize_ready h.1.1.left),
      HPrime.finalize_keeps v t (finalize_ready h.1.1.right)⟩)
  exact result.mono (fun _ _ h => h) (fun _ _ h => h.1)

theorem finishOutput_rel : RelCT isa Related
    (.block ([Impl.Argon2.AArch64.Instructions.mov .x22 .x19, Impl.Argon2.AArch64.Instructions.imm .x8 64].flatten))
      (HPrime.AgreeRegs [.x24, .x22, .x8]) := by
  have ct := (RelCT.taint (A := taint) (P := Related) (Taint.ofRegs [])
    (fun _ _ hp => ⟨hp.sp, by simp [Taint.ofRegs]⟩)
    (c := .block ([Impl.Argon2.AArch64.Instructions.mov .x22 .x19, Impl.Argon2.AArch64.Instructions.imm .x8 64].flatten)) (by taint_decide)).wpDep
    (fun s t _ => ⟨finishOutput_ok s, finishOutput_ok t⟩)
  apply ct.mono (fun _ _ h => h)
  rintro a b ⟨_, s, t, hp, ⟨da, la, _, ka⟩, ⟨db, lb, _, kb⟩⟩
  refine ⟨by rw [ka.sp, kb.sp, hp.sp], ?_⟩
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · rw [ka.x24, kb.x24, hp.bx]
  · rw [da, db, hp.bp]
  · rw [la, lb]

theorem copy_digest_rel : RelCT isa (HPrime.AgreeRegs [.x24, .x22, .x8])
    Impl.Argon2.AArch64.HPrime.copy (fun _ _ => True) :=
  RelCT.taint (A := taint) (Taint.ofRegs [.x24, .x22, .x8])
    (fun _ _ h => h.taint) (by taint_decide)

theorem finish_rel (v : HPrime.Backend) :
    RelCT isa (RelatedRegs [.x20]) (finish v.hash) (fun _ _ => True) :=
  finishCount_rel.seq ((finalize_hash_rel v).seq (finishOutput_rel.seq copy_digest_rel))

end VG.Proof.Argon2.AArch64.Initial
