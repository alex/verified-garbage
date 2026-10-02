import VerifiedGarbage.Proof.Argon2.X86_64.InitialCTState

/-! H₀ finalization and its fixed-size digest copy reveal no input contents. -/

namespace VG.Proof.Argon2.X86_64.Initial

open VG VG.X86_64 VG.Impl.Argon2.X86_64.Initial

theorem finishCount_rel : RelCT isa (RelatedRegs [.r12]) (.block [.mov .rsi (.reg .r12)])
    (fun s t => RelatedRegs [.r12] s t ∧ s.gpr .rsi = t.gpr .rsi) := by
  have ct := (RelCT.taint (A := taint) (P := RelatedRegs [.r12]) (Taint.ofRegs [])
    (fun _ _ _ => Taint.agree_ofRegs (by simp))
    (c := .block [.mov .rsi (.reg .r12)]) (by taint_decide)).wpDep
    (fun s t _ => ⟨finishCount_ok s, finishCount_ok t⟩)
  apply ct.mono (fun _ _ h => h)
  rintro a b ⟨_, s, t, hp, ⟨ca, _, ka⟩, ⟨cb, _, kb⟩⟩
  refine ⟨⟨hp.1.keeps (Keeps.of_hash ka) (Keeps.of_hash kb), ?_⟩, ?_⟩
  · intro r hr
    simp only [List.mem_singleton] at hr; subst r
    rw [ka.regs .r12 (by decide), kb.regs .r12 (by decide)]
    exact hp.2 _ (by simp)
  · rw [ca, cb]; exact hp.2 _ (by simp)

theorem finalize_hash_rel (v : Proof.Blake2.X86_64.Backend) :
    RelCT isa (fun s t => RelatedRegs [.r12] s t ∧ s.gpr .rsi = t.gpr .rsi)
      (Impl.Argon2.X86_64.HPrime.finalize (HPrime.hash v)) Related := by
  have ct := HPrime.finalize_rel v (P := fun s t => RelatedRegs [.r12] s t ∧ s.gpr .rsi = t.gpr .rsi)
    (fun s t h => ⟨finalize_ready h.1.1.left, finalize_ready h.1.1.right, h.1.1.bx, h.2, h.1.1.sp⟩)
  have result := hash_keeps_rel [] (by simp) ct (fun _ _ h => ⟨h.1.1, by simp [HPrime.AgreeRegs]⟩)
    (fun s t h => ⟨HPrime.finalize_keeps v s (finalize_ready h.1.1.left),
      HPrime.finalize_keeps v t (finalize_ready h.1.1.right)⟩)
  exact result.mono (fun _ _ h => h) (fun _ _ h => h.1)

theorem finishOutput_rel : RelCT isa Related
    (.block [.mov .r14 (.reg .rbp), .mov32 .rax (.imm 64)])
      (HPrime.AgreeRegs [.rbx, .r14, .rax]) := by
  have ct := (RelCT.taint (A := taint) (P := Related) (Taint.ofRegs [])
    (fun _ _ _ => Taint.agree_ofRegs (by simp))
    (c := .block [.mov .r14 (.reg .rbp), .mov32 .rax (.imm 64)]) (by taint_decide)).wpDep
    (fun s t _ => ⟨finishOutput_ok s, finishOutput_ok t⟩)
  apply ct.mono (fun _ _ h => h)
  rintro a b ⟨_, s, t, hp, ⟨da, la, _, ka⟩, ⟨db, lb, _, kb⟩⟩ r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · rw [ka.rbx, kb.rbx, hp.bx]
  · rw [da, db, hp.bp]
  · rw [la, lb]

theorem copy_digest_rel : RelCT isa (HPrime.AgreeRegs [.rbx, .r14, .rax])
    Impl.Argon2.X86_64.HPrime.copy (fun _ _ => True) :=
  RelCT.taint (A := taint) (Taint.ofRegs [.rbx, .r14, .rax])
    (fun _ _ h => Taint.agree_ofRegs h) (by taint_decide)

theorem finish_rel (v : Proof.Blake2.X86_64.Backend) :
    RelCT isa (RelatedRegs [.r12]) (finish (HPrime.hash v)) (fun _ _ => True) :=
  finishCount_rel.seq ((finalize_hash_rel v).seq (finishOutput_rel.seq copy_digest_rel))

end VG.Proof.Argon2.X86_64.Initial
