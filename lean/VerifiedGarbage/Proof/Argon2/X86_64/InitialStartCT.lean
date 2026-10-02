import VerifiedGarbage.Proof.Argon2.X86_64.InitialCTState

/-! H₀ initialization and its fixed parameter header have input-independent traces. -/

namespace VG.Proof.Argon2.X86_64.Initial

open VG VG.X86_64 VG.Impl.Argon2.X86_64.Initial

theorem digestLength_rel : RelCT isa Related (.block [.mov32 .rsi (.imm 64)])
    (fun s t => Related s t ∧ s.gpr .rsi = 64 ∧ t.gpr .rsi = 64) := by
  have ct := (RelCT.taint (A := taint) (P := Related) (Taint.ofRegs [])
    (fun _ _ _ => Taint.agree_ofRegs (by simp))
    (c := .block [.mov32 .rsi (.imm 64)]) (by taint_decide)).wpDep
    (fun s t _ => ⟨digestLength_ok s, digestLength_ok t⟩)
  apply ct.mono (fun _ _ h => h)
  rintro a b ⟨_, s, t, hp, ⟨la, _, ka⟩, ⟨lb, _, kb⟩⟩
  exact ⟨hp.keeps (Keeps.of_hash ka) (Keeps.of_hash kb), la, lb⟩

theorem init_hash_rel (v : Proof.Blake2.X86_64.Backend) :
    RelCT isa (fun s t => Related s t ∧ s.gpr .rsi = 64 ∧ t.gpr .rsi = 64)
      (Impl.Argon2.X86_64.HPrime.init (HPrime.hash v)) Related := by
  have ready (s : State) (h : Ready s) (len : s.gpr .rsi = 64) : HPrime.InitReady s :=
    ⟨by rw [len]; decide, h.space.work,
      (h.space.stackWork.sub_left (below_sub (by decide) (by decide))).sub_right (Region.sub_prefix (by decide))⟩
  have ct := HPrime.init_rel v (P := fun s t => Related s t ∧ s.gpr .rsi = 64 ∧ t.gpr .rsi = 64)
    (fun s t ⟨h, ls, lt⟩ => ⟨ready s h.left ls, ready t h.right lt,
      h.bx, ls.trans lt.symm, h.sp⟩)
  have result := hash_keeps_rel [] (by simp) ct (fun _ _ h => ⟨h.1, by simp [HPrime.AgreeRegs]⟩)
    (fun s t ⟨h, ls, lt⟩ => ⟨HPrime.init_keeps v s (ready s h.left ls), HPrime.init_keeps v t (ready t h.right lt)⟩)
  exact result.mono (fun _ _ h => h) (fun _ _ h => h.1)

theorem header_state_rel : RelCT isa Related headerCode Related := by
  have ct := (header_rel.mono (P' := Related) (fun _ _ h => ⟨h.bp, h.bx⟩)
    (fun _ _ h => h)).wpDep (fun s t h =>
      ⟨headerWords_ok s 6 (by decide) h.left.space, headerWords_ok t 6 (by decide) h.right.space⟩)
  exact ct.mono (fun _ _ h => h) (fun _ _ ⟨_, _, _, hp, ⟨_, ka⟩, ⟨_, kb⟩⟩ => hp.keeps ka kb)

theorem fixed_header_rel (v : Proof.Blake2.X86_64.Backend) :
    RelCT isa Related (Impl.Argon2.X86_64.HPrime.absorbFixed (HPrime.hash v) 768 24) Related := by
  have args := (RelCT.taint (A := taint) (P := Related) (Taint.ofRegs [])
    (fun _ _ _ => Taint.agree_ofRegs (by simp))
    (c := .block (Impl.Argon2.X86_64.HPrime.fixedArgs 768 24)) (by taint_decide)).wpDep
    (fun s t _ => ⟨HPrime.fixedArgs_ok s 768 24 (by decide) (by decide),
      HPrime.fixedArgs_ok t 768 24 (by decide) (by decide)⟩)
  have call := HPrime.update_rel v (P := fun a b => True ∧ ∃ s t, Related s t ∧
      HPrime.FixedArgs s a 768 24 ∧ HPrime.FixedArgs t b 768 24)
    (fun a b ⟨_, s, t, hp, ha, hb⟩ => ⟨HPrime.fixed_ready (finalize_ready hp.left) ha (by decide) (by decide),
      HPrime.fixed_ready (finalize_ready hp.right) hb (by decide) (by decide),
      by rw [ha.keeps.rbx, hb.keeps.rbx, hp.bx], by rw [ha.count, hb.count],
      by rw [ha.data, hb.data, hp.bx], by rw [ha.size, hb.size], by rw [ha.keeps.rsp, hb.keeps.rsp, hp.sp]⟩)
  have ct := args.seq call
  have result := hash_keeps_rel [] (by simp) ct (fun _ _ h => ⟨h, by simp [HPrime.AgreeRegs]⟩)
    (fun s t h => ⟨HPrime.absorbFixed_keeps v s 768 24 (finalize_ready h.left) (by decide) (by decide),
      HPrime.absorbFixed_keeps v t 768 24 (finalize_ready h.right) (by decide) (by decide)⟩)
  exact result.mono (fun _ _ h => h) (fun _ _ h => h.1)

theorem initialCount_rel : RelCT isa Related (.block [.mov32 .r12 (.imm 24)]) (RelatedRegs [.r12]) := by
  have ct := (RelCT.taint (A := taint) (P := Related) (Taint.ofRegs [])
    (fun _ _ _ => Taint.agree_ofRegs (by simp))
    (c := .block [.mov32 .r12 (.imm 24)]) (by taint_decide)).wpDep
    (fun s t _ => ⟨initialCount_ok s, initialCount_ok t⟩)
  apply ct.mono (fun _ _ h => h)
  rintro a b ⟨_, s, t, hp, ⟨la, _, ka⟩, ⟨lb, _, kb⟩⟩
  refine ⟨hp.keeps ka kb, ?_⟩
  intro r hr
  simp only [List.mem_singleton] at hr; subst r
  exact la.trans lb.symm

theorem start_rel (v : Proof.Blake2.X86_64.Backend) :
    RelCT isa Related (start (HPrime.hash v)) (RelatedRegs [.r12]) :=
  digestLength_rel.seq ((init_hash_rel v).seq (header_state_rel.seq
    ((fixed_header_rel v).seq initialCount_rel)))

end VG.Proof.Argon2.X86_64.Initial
