import VerifiedGarbage.Proof.Argon2.AArch64.HPrime.Fixed
import VerifiedGarbage.Proof.Argon2.AArch64.HPrime.Copy
import VerifiedGarbage.Proof.Argon2.AArch64.HPrime.RelCT
import VerifiedGarbage.Proof.Argon2.AArch64.HPrime.Finalize
import VerifiedGarbage.Proof.Argon2.AArch64.HPrime.Frame
import VerifiedGarbage.Proof.Argon2.AArch64.HPrime.Init
import VerifiedGarbage.Proof.Argon2.AArch64.HPrime.Update

/-! Merged from `Proof.Argon2.AArch64.HPrime.UpdateCT`. -/
section
/-! # H′: constant time of a BLAKE2b update -/

namespace VG.Proof.Argon2.AArch64.HPrime

open VG VG.AArch64 VG.Impl.Argon2.AArch64.HPrime

structure UpdateReady (s : State) : Prop where
  spBound : 16 ≤ s.sp.toNat
  work : (⟨s.gpr .x24, 16384⟩ : Region) ∈ s.wr
  data : Covers [⟨s.gpr .x2, (s.gpr .x3).toNat⟩] (s.rd ++ s.wr)
  dataState : (⟨s.gpr .x2, (s.gpr .x3).toNat⟩ : Region).Disjoint ⟨s.gpr .x24, 192⟩
  dataScratch : (⟨s.gpr .x2, (s.gpr .x3).toNat⟩ : Region).Disjoint ⟨s.gpr .x24 + 192, 576⟩
  stackWork : (below (s.sp) 16).Disjoint ⟨s.gpr .x24, 16384⟩
  stackData : (below (s.sp) 16).Disjoint ⟨s.gpr .x2, (s.gpr .x3).toNat⟩

theorem update_keeps (v : Backend) (s : State) (h : UpdateReady s) :
    WP isa (update v.hash) s (Keeps s) := by
  unfold update
  refine WP.seq ((updateArgs_ok s).mono fun u hu => ?_)
  obtain ⟨pre, cover, writes⟩ := update_call_hyps s u hu h.spBound h.work h.data
    h.dataState h.dataScratch h.stackWork h.stackData
  refine WP.callF (k := Proof.Blake2.updateAArch64 Spec.Blake2.b) v.updateCorrect
    pre cover writes ?_ (by rw [v.ok.updateDepth]; decide)
  intro t rd wr sp frame regs _
  refine ⟨fun r hr h30 => ?_, rd.trans hu.rd, wr.trans hu.wr, sp.trans hu.sp, ?_⟩
  · have hn : r ≠ .x0 ∧ r ≠ .x4 := by
      simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    exact (regs r hr h30).trans (hu.other r hn.1 hn.2)
  · apply update_frame
    simpa only [v.ok.updateDepth, hu.sp, hu.mem,
      List.cons_append, List.nil_append] using frame

theorem update_rel (v : Backend) {P : State → State → Prop}
    (hP : ∀ s₁ s₂, P s₁ s₂ → UpdateReady s₁ ∧ UpdateReady s₂ ∧
      s₁.gpr .x24 = s₂.gpr .x24 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.gpr .x2 = s₂.gpr .x2 ∧
      s₁.gpr .x3 = s₂.gpr .x3 ∧ s₁.sp = s₂.sp) :
    RelCT isa P (update v.hash) fun _ _ => True := by
  have args := (RelCT.taint (A := taint) (P := P) (Taint.ofRegs [])
    (fun _ _ hp => ⟨(hP _ _ hp).2.2.2.2.2.2, by simp [Taint.ofRegs]⟩) (c := .block updateArgs) (by taint_decide)).wpDep
    (F := UpdateArgs) fun s₁ s₂ _ => ⟨updateArgs_ok s₁, updateArgs_ok s₂⟩
  have call := RelCT.callEx (n := v.hash.updateName) (k := Proof.Blake2.updateAArch64 Spec.Blake2.b)
    (P := fun s₁ s₂ => True ∧ ∃ σ₁ σ₂, P σ₁ σ₂ ∧ UpdateArgs σ₁ s₁ ∧ UpdateArgs σ₂ s₂)
    v.updateCorrect v.updateCT
    fun s₁ s₂ ⟨_, σ₁, σ₂, hp, h₁, h₂⟩ => by
      obtain ⟨p₁, p₂, base, count, data, len, sp⟩ := hP _ _ hp
      obtain ⟨pre₁, cover₁, writes₁⟩ := update_call_hyps σ₁ s₁ h₁ p₁.spBound p₁.work p₁.data
        p₁.dataState p₁.dataScratch p₁.stackWork p₁.stackData
      obtain ⟨pre₂, cover₂, writes₂⟩ := update_call_hyps σ₂ s₂ h₂ p₂.spBound p₂.work p₂.data
        p₂.dataState p₂.dataScratch p₂.stackWork p₂.stackData
      have sp' : s₁.sp = s₂.sp := h₁.sp.trans (sp.trans h₂.sp.symm)
      refine ⟨_, _, _, _, pre₁, pre₂, ?_, cover₁, writes₁, cover₂, writes₂⟩
      simp only [Proof.Blake2.updateAArch64, State.withRegions_gpr,
        State.callEntry_gpr _ (by decide : Reg.x0 ∉ linkRegs),
        State.callEntry_gpr _ (by decide : Reg.x1 ∉ linkRegs),
        State.callEntry_gpr _ (by decide : Reg.x2 ∉ linkRegs),
        State.callEntry_gpr _ (by decide : Reg.x3 ∉ linkRegs),
        State.callEntry_gpr _ (by decide : Reg.x4 ∉ linkRegs), State.callEntry_sp, State.withRegions_sp]
      exact ⟨by rw [h₁.state, h₂.state, base],
        by rw [h₁.other _ (by decide) (by decide), h₂.other _ (by decide) (by decide), count],
        by rw [h₁.other _ (by decide) (by decide), h₂.other _ (by decide) (by decide), data],
        by rw [h₁.other _ (by decide) (by decide), h₂.other _ (by decide) (by decide), len],
        by rw [h₁.scratch, h₂.scratch, base], by rw [sp']⟩
  exact args.seq call

end VG.Proof.Argon2.AArch64.HPrime
end

/-! Merged from `Proof.Argon2.AArch64.HPrime.RelatedCT`. -/
section
/-! Merged from `Proof.Argon2.AArch64.HPrime.InitCT`. -/
section
/-! # H′: constant time of BLAKE2b initialization -/

namespace VG.Proof.Argon2.AArch64.HPrime

open VG VG.AArch64 VG.Impl.Argon2.AArch64.HPrime

structure InitReady (s : State) : Prop where
  length : 1 ≤ (s.gpr .x1).toNat ∧ (s.gpr .x1).toNat ≤ 64
  work : (⟨s.gpr .x24, 16384⟩ : Region) ∈ s.wr
  stack : (below (s.sp) 8).Disjoint ⟨s.gpr .x24, 192⟩

theorem init_keeps (v : Backend) (s : State) (h : InitReady s) :
    WP isa (init v.hash) s (Keeps s) :=
  (init_ok v s h.length h.work).mono fun _ ⟨_, regs, rd, wr, sp, frame⟩ =>
    ⟨regs, rd, wr, sp, init_frame _ _ frame⟩

theorem init_rel (v : Backend) {P : State → State → Prop}
    (hP : ∀ s₁ s₂, P s₁ s₂ → InitReady s₁ ∧ InitReady s₂ ∧
      s₁.gpr .x24 = s₂.gpr .x24 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.sp = s₂.sp) :
    RelCT isa P (init v.hash) fun _ _ => True := by
  have args := (RelCT.taint (A := taint) (P := P) (Taint.ofRegs [])
    (fun _ _ hp => ⟨(hP _ _ hp).2.2.2.2, by simp [Taint.ofRegs]⟩) (c := .block initArgs) (by taint_decide)).wpDep
    (F := InitArgs) fun s₁ s₂ _ => ⟨initArgs_ok s₁, initArgs_ok s₂⟩
  have call := RelCT.callEx (n := v.hash.initName) (k := Proof.Blake2.initAArch64 Spec.Blake2.b)
    (P := fun s₁ s₂ => True ∧ ∃ σ₁ σ₂, P σ₁ σ₂ ∧ InitArgs σ₁ s₁ ∧ InitArgs σ₂ s₂)
    v.initCorrect v.initCT
    fun s₁ s₂ ⟨_, σ₁, σ₂, hp, h₁, h₂⟩ => by
      obtain ⟨p₁, p₂, base, len, sp⟩ := hP _ _ hp
      obtain ⟨pre₁, cover₁, writes₁⟩ := init_call_hyps σ₁ s₁ h₁ p₁.length p₁.work
      obtain ⟨pre₂, cover₂, writes₂⟩ := init_call_hyps σ₂ s₂ h₂ p₂.length p₂.work
      refine ⟨_, _, _, _, pre₁, pre₂, ?_, cover₁, writes₁, cover₂, writes₂⟩
      · simp only [Proof.Blake2.initAArch64, State.withRegions_gpr,
          State.callEntry_gpr _ (by decide : Reg.x0 ∉ linkRegs),
          State.callEntry_gpr _ (by decide : Reg.x1 ∉ linkRegs),
          State.callEntry_gpr _ (by decide : Reg.x2 ∉ linkRegs),
          State.callEntry_gpr _ (by decide : Reg.x3 ∉ linkRegs)]
        exact ⟨by rw [h₁.state, h₂.state, base],
          by rw [h₁.other _ (by decide) (by decide) (by decide),
            h₂.other _ (by decide) (by decide) (by decide), len],
          by rw [h₁.key, h₂.key, base], by rw [h₁.keylen, h₂.keylen], h₁.sp.trans (sp.trans h₂.sp.symm)⟩
  exact args.seq call

end VG.Proof.Argon2.AArch64.HPrime
end

/-! Merged from `Proof.Argon2.AArch64.HPrime.FinalizeCT`. -/
section
/-! # H′: constant time of BLAKE2b finalization -/

namespace VG.Proof.Argon2.AArch64.HPrime

open VG VG.AArch64 VG.Impl.Argon2.AArch64.HPrime

structure FinalizeReady (s : State) : Prop where
  spBound : 16 ≤ s.sp.toNat
  work : (⟨s.gpr .x24, 16384⟩ : Region) ∈ s.wr
  stack : (below (s.sp) 16).Disjoint ⟨s.gpr .x24, 16384⟩

theorem FinalizeReady.keeps {s t : State} (h : FinalizeReady s) (k : Keeps s t) : FinalizeReady t := by
  refine ⟨by rw [k.sp]; exact h.spBound, ?_, ?_⟩
  · rw [k.wr, k.x24]; exact h.work
  · rw [k.sp, k.x24]; exact h.stack

theorem finalize_keeps (v : Backend) (s : State) (h : FinalizeReady s) :
    WP isa (finalize v.hash) s (Keeps s) := by
  unfold finalize
  refine WP.seq ((finalizeArgs_ok s).mono fun u hu => ?_)
  obtain ⟨pre, cover, writes⟩ := finalize_call_hyps s u hu h.spBound h.work h.stack
  refine WP.callF (k := Proof.Blake2.finalizeAArch64 Spec.Blake2.b) v.finalizeCorrect
    pre cover writes ?_ (by rw [v.ok.finalizeDepth]; decide)
  intro t rd wr sp frame regs _
  refine ⟨fun r hr h30 => ?_, rd.trans hu.rd, wr.trans hu.wr, sp.trans hu.sp, ?_⟩
  · have hn : r ≠ .x0 ∧ r ≠ .x2 ∧ r ≠ .x3 := by
      simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    exact (regs r hr h30).trans (hu.other r hn.1 hn.2.1 hn.2.2)
  · apply finalize_frame
    simpa only [v.ok.finalizeDepth, hu.sp, hu.mem,
      List.cons_append, List.nil_append] using frame

theorem finalize_rel (v : Backend) {P : State → State → Prop}
    (hP : ∀ s₁ s₂, P s₁ s₂ → FinalizeReady s₁ ∧ FinalizeReady s₂ ∧
      s₁.gpr .x24 = s₂.gpr .x24 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.sp = s₂.sp) :
    RelCT isa P (finalize v.hash) fun _ _ => True := by
  have args := (RelCT.taint (A := taint) (P := P) (Taint.ofRegs [])
    (fun _ _ hp => ⟨(hP _ _ hp).2.2.2.2, by simp [Taint.ofRegs]⟩) (c := .block finalizeArgs) (by taint_decide)).wpDep
    (F := FinalizeArgs) fun s₁ s₂ _ => ⟨finalizeArgs_ok s₁, finalizeArgs_ok s₂⟩
  have call := RelCT.callEx (n := v.hash.finalizeName) (k := Proof.Blake2.finalizeAArch64 Spec.Blake2.b)
    (P := fun s₁ s₂ => True ∧ ∃ σ₁ σ₂, P σ₁ σ₂ ∧ FinalizeArgs σ₁ s₁ ∧ FinalizeArgs σ₂ s₂)
    v.finalizeCorrect v.finalizeCT
    fun s₁ s₂ ⟨_, σ₁, σ₂, hp, h₁, h₂⟩ => by
      obtain ⟨p₁, p₂, base, count, sp⟩ := hP _ _ hp
      obtain ⟨pre₁, cover₁, writes₁⟩ := finalize_call_hyps σ₁ s₁ h₁ p₁.spBound p₁.work p₁.stack
      obtain ⟨pre₂, cover₂, writes₂⟩ := finalize_call_hyps σ₂ s₂ h₂ p₂.spBound p₂.work p₂.stack
      have sp' : s₁.sp = s₂.sp := h₁.sp.trans (sp.trans h₂.sp.symm)
      refine ⟨_, _, _, _, pre₁, pre₂, ?_, cover₁, writes₁, cover₂, writes₂⟩
      simp only [Proof.Blake2.finalizeAArch64, State.withRegions_gpr,
        State.callEntry_gpr _ (by decide : Reg.x0 ∉ linkRegs),
        State.callEntry_gpr _ (by decide : Reg.x1 ∉ linkRegs),
        State.callEntry_gpr _ (by decide : Reg.x2 ∉ linkRegs),
        State.callEntry_gpr _ (by decide : Reg.x3 ∉ linkRegs), State.callEntry_sp, State.withRegions_sp]
      exact ⟨by rw [h₁.state, h₂.state, base],
        by rw [h₁.other _ (by decide) (by decide) (by decide),
          h₂.other _ (by decide) (by decide) (by decide), count],
        by rw [h₁.digest, h₂.digest, base], by rw [h₁.scratch, h₂.scratch, base], by rw [sp']⟩
  exact args.seq call

end VG.Proof.Argon2.AArch64.HPrime
end

/-! Merged from `Proof.Argon2.AArch64.HPrime.BlocksCT`. -/
section
/-! # H′: constant time of public argument handling and copying -/

namespace VG.Proof.Argon2.AArch64.HPrime

open VG VG.AArch64 VG.Impl.Argon2.AArch64.HPrime

def publicRegs : List Reg := [.x24, .x20, .x21, .x22, .x23]
def AgreeRegs (rs : List Reg) (s t : State) : Prop :=
  s.sp = t.sp ∧ ∀ r ∈ rs, s.gpr r = t.gpr r

theorem AgreeRegs.taint {rs : List Reg} {s t : State} (h : AgreeRegs rs s t) :
    AArch64.Taint.Agree (Taint.ofRegs rs) s t :=
  ⟨h.1, fun r hr => h.2 r (Taint.mem_ofRegs.mp hr)⟩

theorem publicRegs_callee : ∀ r ∈ publicRegs, r ∈ preserved := by decide

theorem publicRegs_not_link : ∀ r ∈ publicRegs, r ≠ .x30 := by decide

theorem setup_rel :
    RelCT isa (AgreeRegs [.x0, .x1, .x2, .x3, .x4]) (.block setup)
      (AgreeRegs publicRegs) :=
  RelCT.taintRegs (τ := Taint.ofRegs [.x0, .x1, .x2, .x3, .x4])
    (fun _ _ hp => hp.taint) publicRegs (by taint_decide)

theorem chooseLength_rel : RelCT isa (AgreeRegs publicRegs) chooseLength
    (AgreeRegs (.x1 :: publicRegs)) :=
  RelCT.taintRegs (τ := Taint.ofRegs publicRegs)
    (fun _ _ hp => hp.taint) (.x1 :: publicRegs) (by taint_decide)

theorem copy_rel : RelCT isa (AgreeRegs (.x8 :: publicRegs)) copy (AgreeRegs publicRegs) :=
  RelCT.taintRegs (τ := Taint.ofRegs (.x8 :: publicRegs))
    (fun _ _ hp => hp.taint) publicRegs (by taint_decide)

theorem emitPrefix_rel : RelCT isa (AgreeRegs publicRegs) emitPrefix (AgreeRegs publicRegs) :=
  RelCT.taintRegs (τ := Taint.ofRegs publicRegs)
    (fun _ _ hp => hp.taint) publicRegs (by taint_decide)

theorem copyRemaining_rel : RelCT isa (AgreeRegs publicRegs) copyRemaining (AgreeRegs publicRegs) :=
  RelCT.taintRegs (τ := Taint.ofRegs publicRegs)
    (fun _ _ hp => hp.taint) publicRegs (by taint_decide)

theorem restore_rel : RelCT isa (AgreeRegs [.x24]) (.block restore) fun _ _ => True :=
  RelCT.taint (A := taint) (Taint.ofRegs [.x24]) (fun _ _ hp => hp.taint)
    (by taint_decide)

end VG.Proof.Argon2.AArch64.HPrime
end

/-! # H′: retaining public caller state across hash calls -/

namespace VG.Proof.Argon2.AArch64.HPrime

open VG VG.AArch64 VG.Impl.Argon2.AArch64.HPrime

/-- Caller conditions that survive hashing in the workspace. -/
structure Stable (F : State → Prop) : Prop where
  ready : ∀ s, F s → FinalizeReady s
  keeps : ∀ s t, F s → Keeps s t → F t

def Related (F : State → Prop) (s t : State) : Prop := F s ∧ F t ∧ AgreeRegs publicRegs s t

theorem Related.keeps {F : State → Prop} (stable : Stable F) {s₁ s₂ t₁ t₂ : State}
    (h : Related F s₁ s₂) (k₁ : Keeps s₁ t₁) (k₂ : Keeps s₂ t₂) : Related F t₁ t₂ := by
  refine ⟨stable.keeps _ _ h.1 k₁, stable.keeps _ _ h.2.1 k₂,
    k₁.sp.trans (h.2.2.1.trans k₂.sp.symm), fun r hr => ?_⟩
  rw [k₁.regs _ (publicRegs_callee r hr) (publicRegs_not_link r hr), k₂.regs _ (publicRegs_callee r hr) (publicRegs_not_link r hr)]
  exact h.2.2.2 r hr

theorem keeps_rel {F : State → Prop} (stable : Stable F) {P : State → State → Prop} {c : Prog isa}
    (ct : RelCT isa P c fun _ _ => True)
    (wp : ∀ s₁ s₂, P s₁ s₂ → WP isa c s₁ (Keeps s₁) ∧ WP isa c s₂ (Keeps s₂))
    (pre : ∀ s₁ s₂, P s₁ s₂ → Related F s₁ s₂) : RelCT isa P c (Related F) :=
  (ct.wpDep wp).mono (fun _ _ h => h) fun _ _ ⟨_, _, _, hp, k₁, k₂⟩ =>
    (pre _ _ hp).keeps stable k₁ k₂

theorem stable_init_rel (v : Backend) {F : State → Prop} (stable : Stable F) :
    RelCT isa (fun s₁ s₂ => Related F s₁ s₂ ∧
      (1 ≤ (s₁.gpr .x1).toNat ∧ (s₁.gpr .x1).toNat ≤ 64) ∧ s₁.gpr .x1 = s₂.gpr .x1)
      (init v.hash) (Related F) := by
  have ready (s : State) (hs : F s) (len : 1 ≤ (s.gpr .x1).toNat ∧ (s.gpr .x1).toNat ≤ 64) :
      InitReady s := by
    have h := stable.ready s hs
    exact ⟨len, h.work, (h.stack.sub_left (below_sub (by decide) (by decide))).sub_right
      (Region.sub_prefix (by decide))⟩
  apply keeps_rel stable (init_rel v ?_) ?_ (fun _ _ h => h.1)
  · intro s₁ s₂ ⟨h, len, eq⟩
    exact ⟨ready s₁ h.1 len, ready s₂ h.2.1 (by rw [← eq]; exact len),
      h.2.2.2 _ (by decide), eq, h.2.2.1⟩
  · intro s₁ s₂ ⟨h, len, eq⟩
    exact ⟨init_keeps v s₁ (ready s₁ h.1 len),
      init_keeps v s₂ (ready s₂ h.2.1 (by rw [← eq]; exact len))⟩

theorem stable_finalize_rel (v : Backend) {F : State → Prop} (stable : Stable F) :
    RelCT isa (fun s₁ s₂ => Related F s₁ s₂ ∧ s₁.gpr .x1 = s₂.gpr .x1)
      (finalize v.hash) (Related F) := by
  apply keeps_rel stable (finalize_rel v ?_) ?_ (fun _ _ h => h.1)
  · intro s₁ s₂ ⟨h, count⟩
    exact ⟨stable.ready _ h.1, stable.ready _ h.2.1,
      h.2.2.2 _ (by decide), count, h.2.2.1⟩
  · intro s₁ s₂ ⟨h, _⟩
    exact ⟨finalize_keeps v s₁ (stable.ready _ h.1), finalize_keeps v s₂ (stable.ready _ h.2.1)⟩

end VG.Proof.Argon2.AArch64.HPrime
end

/-! # H′: constant time of hashing a fixed workspace buffer -/

namespace VG.Proof.Argon2.AArch64.HPrime

open VG VG.AArch64 VG.Impl.Argon2.AArch64.HPrime

theorem FixedArgs.keeps {s t : State} {offset size : Nat} (h : FixedArgs s t offset size) : Keeps s t := by
  refine ⟨fun r hr _ => ?_, h.rd, h.wr, h.sp, ?_⟩
  · have hn : r ≠ .x1 ∧ r ≠ .x2 ∧ r ≠ .x3 := by
      simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    exact h.other r hn.1 hn.2.1 hn.2.2
  · rw [h.mem]; exact Frame.refl _ _

theorem fixed_ready {s t : State} {offset size : Nat} (ready : FinalizeReady s)
    (h : FixedArgs s t offset size) (lo : 768 ≤ offset) (hi : offset + size ≤ 16384) :
    UpdateReady t := by
  have k := h.keeps
  have len : (t.gpr .x3).toNat = size := by
    rw [h.size, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  refine ⟨(ready.keeps k).spBound, (ready.keeps k).work, ?_, ?_, ?_, (ready.keeps k).stack, ?_⟩
  · apply Covers.of_sub
    intro r hr
    simp only [List.mem_singleton] at hr; subst r
    refine ⟨⟨s.gpr .x24, 16384⟩, List.mem_append_right _ (k.wr.symm ▸ ready.work), offset, h.data, ?_⟩
    change offset + (t.gpr .x3).toNat ≤ 16384
    rw [len]; exact hi
  · rw [h.data, len, k.x24]
    exact (Offset.base_disjoint _ (by omega) (by omega)).symm
  · rw [h.data, len, k.x24]
    exact Offset.disjoint _ (d := offset) (n := size) (e := 192) (k := 576) (by omega) (by omega) (by decide)
  · rw [k.sp, h.data, len]
    exact ready.stack.sub_right (Offset.sub_base _ hi)

theorem absorbFixed_keeps (v : Backend) (s : State) (offset size : Nat)
    (ready : FinalizeReady s) (offsetBound : offset < 4096) (lo : 768 ≤ offset) (hi : offset + size ≤ 16384) :
    WP isa (absorbFixed v.hash offset size) s (Keeps s) := by
  unfold absorbFixed
  refine WP.seq ((fixedArgs_ok s offset size offsetBound (by omega)).mono fun u hu => ?_)
  exact (update_keeps v u (fixed_ready ready hu lo hi)).mono fun _ h => hu.keeps.trans h

theorem absorbFixed_rel (v : Backend) (offset size : Nat)
    (offsetBound : offset < 4096) (lo : 768 ≤ offset) (hi : offset + size ≤ 16384)
    (ct : ∃ hint, (taint.check (Taint.ofRegs []) (.block (fixedArgs offset size)) hint).isSome = true)
    {F : State → Prop} (stable : Stable F) :
    RelCT isa (Related F) (absorbFixed v.hash offset size) (Related F) := by
  obtain ⟨_, ct⟩ := ct
  have args := (RelCT.taint (A := taint) (P := Related F) (Taint.ofRegs [])
    (fun _ _ hp => ⟨hp.2.2.1, by simp [Taint.ofRegs]⟩) (c := .block (fixedArgs offset size))
    ct).wpDep (F := fun s t => FixedArgs s t offset size)
    fun s₁ s₂ _ => ⟨fixedArgs_ok s₁ offset size offsetBound (by omega),
      fixedArgs_ok s₂ offset size offsetBound (by omega)⟩
  have call := update_rel v (P := fun s₁ s₂ => True ∧
      ∃ σ₁ σ₂, Related F σ₁ σ₂ ∧ FixedArgs σ₁ s₁ offset size ∧ FixedArgs σ₂ s₂ offset size)
    fun s₁ s₂ ⟨_, σ₁, σ₂, hp, h₁, h₂⟩ => by
      have base := hp.2.2.2 .x24 (by decide)
      have sp := hp.2.2.1
      exact ⟨fixed_ready (stable.ready _ hp.1) h₁ lo hi, fixed_ready (stable.ready _ hp.2.1) h₂ lo hi,
        by rw [h₁.keeps.x24, h₂.keeps.x24, base], by rw [h₁.count, h₂.count],
        by rw [h₁.data, h₂.data, base], by rw [h₁.size, h₂.size], by rw [h₁.keeps.sp, h₂.keeps.sp, sp]⟩
  exact keeps_rel stable (args.seq call)
    (fun s₁ s₂ hp => ⟨absorbFixed_keeps v s₁ offset size (stable.ready _ hp.1) offsetBound lo hi,
      absorbFixed_keeps v s₂ offset size (stable.ready _ hp.2.1) offsetBound lo hi⟩) (fun _ _ h => h)

end VG.Proof.Argon2.AArch64.HPrime
