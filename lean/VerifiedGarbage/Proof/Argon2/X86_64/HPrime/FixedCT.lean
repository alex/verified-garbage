import VerifiedGarbage.Proof.Argon2.X86_64.HPrime.Fixed
import VerifiedGarbage.Proof.Argon2.X86_64.HPrime.Copy
import VerifiedGarbage.Proof.Framework.X86_64.RelCT
import VerifiedGarbage.Proof.Argon2.X86_64.HPrime.Finalize
import VerifiedGarbage.Proof.Argon2.X86_64.HPrime.Frame
import VerifiedGarbage.Proof.Argon2.X86_64.HPrime.Init
import VerifiedGarbage.Proof.Argon2.X86_64.HPrime.Update

/-! Merged from `Proof.Argon2.X86_64.HPrime.UpdateCT`. -/
section
/-! # H′: constant time of a BLAKE2b update -/

namespace VG.Proof.Argon2.X86_64.HPrime

open VG VG.X86_64 VG.Impl.Argon2.X86_64.HPrime

structure UpdateReady (s : State) : Prop where
  work : (⟨s.gpr .rbx, 16384⟩ : Region) ∈ s.wr
  data : Covers [⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩] (s.rd ++ s.wr)
  dataState : (⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩ : Region).Disjoint ⟨s.gpr .rbx, 192⟩
  dataScratch : (⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩ : Region).Disjoint ⟨s.gpr .rbx + 192, 576⟩
  stackWork : (below (s.gpr .rsp) 16).Disjoint ⟨s.gpr .rbx, 16384⟩
  stackData : (below (s.gpr .rsp) 16).Disjoint ⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩

theorem update_keeps (v : Proof.Blake2.X86_64.Backend) (s : State) (h : UpdateReady s) :
    WP isa (update (hash v)) s (Keeps s) := by
  unfold update
  refine WP.seq ((updateArgs_ok s).mono fun u hu => ?_)
  obtain ⟨pre, cover, writes⟩ := update_call_hyps s u hu h.work h.data
    h.dataState h.dataScratch h.stackWork h.stackData
  refine WP.call (k := Proof.Blake2.updateX86_64 Spec.Blake2.b) v.update_correct (hash_ok v).updateNoSp
    (by change 8 * (hash v).update.depth + 16 < 2 ^ 64; rw [(hash_ok v).updateDepth]; decide)
    pre cover writes ?_
  intro t rd wr regs frame _ _
  refine ⟨fun r hr => ?_, rd.trans hu.rd, wr.trans hu.wr, ?_⟩
  · have hn : r ≠ .rdi ∧ r ≠ .r8 := by
      simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    exact (regs r hr).trans (hu.other r hn.1 hn.2)
  · apply update_frame
    change Frame (_ ++ [below (u.gpr .rsp) (8 * ((hash v).update.depth + 1))]) u.mem t.mem at frame
    simpa only [(hash_ok v).updateDepth, hu.other .rsp (by decide) (by decide), hu.mem,
      List.cons_append, List.nil_append] using frame

theorem update_rel (v : Proof.Blake2.X86_64.Backend) {P : State → State → Prop}
    (hP : ∀ s₁ s₂, P s₁ s₂ → UpdateReady s₁ ∧ UpdateReady s₂ ∧
      s₁.gpr .rbx = s₂.gpr .rbx ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rdx = s₂.gpr .rdx ∧
      s₁.gpr .rcx = s₂.gpr .rcx ∧ s₁.gpr .rsp = s₂.gpr .rsp) :
    RelCT isa P (update (hash v)) fun _ _ => True := by
  have args := (RelCT.taint (A := taint) (P := P) (Taint.ofRegs [])
    (fun _ _ _ => Taint.agree_ofRegs (by simp)) (c := .block updateArgs) (by taint_decide)).wpDep
    (F := UpdateArgs) fun s₁ s₂ _ => ⟨updateArgs_ok s₁, updateArgs_ok s₂⟩
  have call := RelCT.callEx (n := (hash v).updateName) (k := Proof.Blake2.updateX86_64 Spec.Blake2.b)
    (P := fun s₁ s₂ => True ∧ ∃ σ₁ σ₂, P σ₁ σ₂ ∧ UpdateArgs σ₁ s₁ ∧ UpdateArgs σ₂ s₂)
    v.update_correct v.updateCT
    fun s₁ s₂ ⟨_, σ₁, σ₂, hp, h₁, h₂⟩ => by
      obtain ⟨p₁, p₂, base, count, data, len, sp⟩ := hP _ _ hp
      obtain ⟨pre₁, cover₁, writes₁⟩ := update_call_hyps σ₁ s₁ h₁ p₁.work p₁.data
        p₁.dataState p₁.dataScratch p₁.stackWork p₁.stackData
      obtain ⟨pre₂, cover₂, writes₂⟩ := update_call_hyps σ₂ s₂ h₂ p₂.work p₂.data
        p₂.dataState p₂.dataScratch p₂.stackWork p₂.stackData
      have sp' : s₁.gpr .rsp = s₂.gpr .rsp := by
        rw [h₁.other _ (by decide) (by decide), h₂.other _ (by decide) (by decide), sp]
      refine ⟨_, _, _, _, pre₁, pre₂, ?_, cover₁, writes₁, cover₂, writes₂, sp'⟩
      simp only [Proof.Blake2.updateX86_64, State.withRegions_gpr,
        State.callEntry_gpr _ (by decide : Reg.rdi ≠ .rsp),
        State.callEntry_gpr _ (by decide : Reg.rsi ≠ .rsp),
        State.callEntry_gpr _ (by decide : Reg.rdx ≠ .rsp),
        State.callEntry_gpr _ (by decide : Reg.rcx ≠ .rsp),
        State.callEntry_gpr _ (by decide : Reg.r8 ≠ .rsp), State.callEntry_rsp]
      exact ⟨by rw [h₁.state, h₂.state, base],
        by rw [h₁.other _ (by decide) (by decide), h₂.other _ (by decide) (by decide), count],
        by rw [h₁.other _ (by decide) (by decide), h₂.other _ (by decide) (by decide), data],
        by rw [h₁.other _ (by decide) (by decide), h₂.other _ (by decide) (by decide), len],
        by rw [h₁.scratch, h₂.scratch, base], by rw [sp']⟩
  exact args.seq call

end VG.Proof.Argon2.X86_64.HPrime
end

/-! Merged from `Proof.Argon2.X86_64.HPrime.RelatedCT`. -/
section
/-! Merged from `Proof.Argon2.X86_64.HPrime.InitCT`. -/
section
/-! # H′: constant time of BLAKE2b initialization -/

namespace VG.Proof.Argon2.X86_64.HPrime

open VG VG.X86_64 VG.Impl.Argon2.X86_64.HPrime

structure InitReady (s : State) : Prop where
  length : 1 ≤ (s.gpr .rsi).toNat ∧ (s.gpr .rsi).toNat ≤ 64
  work : (⟨s.gpr .rbx, 16384⟩ : Region) ∈ s.wr
  stack : (below (s.gpr .rsp) 8).Disjoint ⟨s.gpr .rbx, 192⟩

theorem init_keeps (v : Proof.Blake2.X86_64.Backend) (s : State) (h : InitReady s) :
    WP isa (init (hash v)) s (Keeps s) :=
  (init_ok v s h.length h.work h.stack).mono fun _ ⟨_, regs, rd, wr, frame⟩ =>
    ⟨regs, rd, wr, init_frame _ _ frame⟩

theorem init_rel (v : Proof.Blake2.X86_64.Backend) {P : State → State → Prop}
    (hP : ∀ s₁ s₂, P s₁ s₂ → InitReady s₁ ∧ InitReady s₂ ∧
      s₁.gpr .rbx = s₂.gpr .rbx ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rsp = s₂.gpr .rsp) :
    RelCT isa P (init (hash v)) fun _ _ => True := by
  have args := (RelCT.taint (A := taint) (P := P) (Taint.ofRegs [])
    (fun _ _ _ => Taint.agree_ofRegs (by simp)) (c := .block initArgs) (by taint_decide)).wpDep
    (F := InitArgs) fun s₁ s₂ _ => ⟨initArgs_ok s₁, initArgs_ok s₂⟩
  have call := RelCT.callEx (n := (hash v).initName) (k := Proof.Blake2.initX86_64 Spec.Blake2.b)
    (P := fun s₁ s₂ => True ∧ ∃ σ₁ σ₂, P σ₁ σ₂ ∧ InitArgs σ₁ s₁ ∧ InitArgs σ₂ s₂)
    Proof.Blake2.X86_64.Stream.initB_correct Proof.Blake2.X86_64.Stream.initB_ct
    fun s₁ s₂ ⟨_, σ₁, σ₂, hp, h₁, h₂⟩ => by
      obtain ⟨p₁, p₂, base, len, sp⟩ := hP _ _ hp
      obtain ⟨pre₁, cover₁, writes₁⟩ := init_call_hyps σ₁ s₁ h₁ p₁.length p₁.work p₁.stack
      obtain ⟨pre₂, cover₂, writes₂⟩ := init_call_hyps σ₂ s₂ h₂ p₂.length p₂.work p₂.stack
      refine ⟨_, _, _, _, pre₁, pre₂, ?_, cover₁, writes₁, cover₂, writes₂, ?_⟩
      · simp only [Proof.Blake2.initX86_64, State.withRegions_gpr,
          State.callEntry_gpr _ (by decide : Reg.rdi ≠ .rsp),
          State.callEntry_gpr _ (by decide : Reg.rsi ≠ .rsp),
          State.callEntry_gpr _ (by decide : Reg.rdx ≠ .rsp),
          State.callEntry_gpr _ (by decide : Reg.rcx ≠ .rsp)]
        exact ⟨by rw [h₁.state, h₂.state, base],
          by rw [h₁.other _ (by decide) (by decide) (by decide),
            h₂.other _ (by decide) (by decide) (by decide), len],
          by rw [h₁.key, h₂.key, base], by rw [h₁.keylen, h₂.keylen]⟩
      · rw [h₁.other _ (by decide) (by decide) (by decide),
          h₂.other _ (by decide) (by decide) (by decide), sp]
  exact args.seq call

end VG.Proof.Argon2.X86_64.HPrime
end

/-! Merged from `Proof.Argon2.X86_64.HPrime.FinalizeCT`. -/
section
/-! # H′: constant time of BLAKE2b finalization -/

namespace VG.Proof.Argon2.X86_64.HPrime

open VG VG.X86_64 VG.Impl.Argon2.X86_64.HPrime

structure FinalizeReady (s : State) : Prop where
  work : (⟨s.gpr .rbx, 16384⟩ : Region) ∈ s.wr
  stack : (below (s.gpr .rsp) 16).Disjoint ⟨s.gpr .rbx, 16384⟩

theorem FinalizeReady.keeps {s t : State} (h : FinalizeReady s) (k : Keeps s t) : FinalizeReady t := by
  constructor
  · rw [k.wr, k.rbx]; exact h.work
  · rw [k.rsp, k.rbx]; exact h.stack

theorem finalize_keeps (v : Proof.Blake2.X86_64.Backend) (s : State) (h : FinalizeReady s) :
    WP isa (finalize (hash v)) s (Keeps s) := by
  unfold finalize
  refine WP.seq ((finalizeArgs_ok s).mono fun u hu => ?_)
  obtain ⟨pre, cover, writes⟩ := finalize_call_hyps s u hu h.work h.stack
  refine WP.call (k := Proof.Blake2.finalizeX86_64 Spec.Blake2.b) v.finalize_correct (hash_ok v).finalizeNoSp
    (by change 8 * (hash v).finalize.depth + 16 < 2 ^ 64; rw [(hash_ok v).finalizeDepth]; decide)
    pre cover writes ?_
  intro t rd wr regs frame _ _
  refine ⟨fun r hr => ?_, rd.trans hu.rd, wr.trans hu.wr, ?_⟩
  · have hn : r ≠ .rdi ∧ r ≠ .rdx ∧ r ≠ .rcx := by
      simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    exact (regs r hr).trans (hu.other r hn.1 hn.2.1 hn.2.2)
  · apply finalize_frame
    change Frame (_ ++ [below (u.gpr .rsp) (8 * ((hash v).finalize.depth + 1))]) u.mem t.mem at frame
    simpa only [(hash_ok v).finalizeDepth, hu.other .rsp (by decide) (by decide) (by decide), hu.mem,
      List.cons_append, List.nil_append] using frame

theorem finalize_rel (v : Proof.Blake2.X86_64.Backend) {P : State → State → Prop}
    (hP : ∀ s₁ s₂, P s₁ s₂ → FinalizeReady s₁ ∧ FinalizeReady s₂ ∧
      s₁.gpr .rbx = s₂.gpr .rbx ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rsp = s₂.gpr .rsp) :
    RelCT isa P (finalize (hash v)) fun _ _ => True := by
  have args := (RelCT.taint (A := taint) (P := P) (Taint.ofRegs [])
    (fun _ _ _ => Taint.agree_ofRegs (by simp)) (c := .block finalizeArgs) (by taint_decide)).wpDep
    (F := FinalizeArgs) fun s₁ s₂ _ => ⟨finalizeArgs_ok s₁, finalizeArgs_ok s₂⟩
  have call := RelCT.callEx (n := (hash v).finalizeName) (k := Proof.Blake2.finalizeX86_64 Spec.Blake2.b)
    (P := fun s₁ s₂ => True ∧ ∃ σ₁ σ₂, P σ₁ σ₂ ∧ FinalizeArgs σ₁ s₁ ∧ FinalizeArgs σ₂ s₂)
    v.finalize_correct v.finalizeCT
    fun s₁ s₂ ⟨_, σ₁, σ₂, hp, h₁, h₂⟩ => by
      obtain ⟨p₁, p₂, base, count, sp⟩ := hP _ _ hp
      obtain ⟨pre₁, cover₁, writes₁⟩ := finalize_call_hyps σ₁ s₁ h₁ p₁.work p₁.stack
      obtain ⟨pre₂, cover₂, writes₂⟩ := finalize_call_hyps σ₂ s₂ h₂ p₂.work p₂.stack
      have sp' : s₁.gpr .rsp = s₂.gpr .rsp := by
        rw [h₁.other _ (by decide) (by decide) (by decide),
          h₂.other _ (by decide) (by decide) (by decide), sp]
      refine ⟨_, _, _, _, pre₁, pre₂, ?_, cover₁, writes₁, cover₂, writes₂, sp'⟩
      simp only [Proof.Blake2.finalizeX86_64, State.withRegions_gpr,
        State.callEntry_gpr _ (by decide : Reg.rdi ≠ .rsp),
        State.callEntry_gpr _ (by decide : Reg.rsi ≠ .rsp),
        State.callEntry_gpr _ (by decide : Reg.rdx ≠ .rsp),
        State.callEntry_gpr _ (by decide : Reg.rcx ≠ .rsp), State.callEntry_rsp]
      exact ⟨by rw [h₁.state, h₂.state, base],
        by rw [h₁.other _ (by decide) (by decide) (by decide),
          h₂.other _ (by decide) (by decide) (by decide), count],
        by rw [h₁.digest, h₂.digest, base], by rw [h₁.scratch, h₂.scratch, base], by rw [sp']⟩
  exact args.seq call

end VG.Proof.Argon2.X86_64.HPrime
end

/-! Merged from `Proof.Argon2.X86_64.HPrime.BlocksCT`. -/
section
/-! # H′: constant time of argument handling and output loops -/

namespace VG.Proof.Argon2.X86_64.HPrime

open VG VG.X86_64 VG.Impl.Argon2.X86_64.HPrime

def publicRegs : List Reg := [.rbx, .r12, .r13, .r14, .r15, .rsp]

def AgreeRegs (rs : List Reg) (s t : State) : Prop := ∀ r ∈ rs, s.gpr r = t.gpr r

theorem publicRegs_callee : ∀ r ∈ publicRegs, r ∈ calleeSaved := by decide

theorem setup_rel :
    RelCT isa (AgreeRegs [.rdi, .rsi, .rdx, .rcx, .r8, .rsp]) (.block setup)
      (AgreeRegs publicRegs) :=
  RelCT.taintRegs (τ := Taint.ofRegs [.rdi, .rsi, .rdx, .rcx, .r8, .rsp])
    (fun _ _ hp => Taint.agree_ofRegs hp) publicRegs (by taint_decide)

theorem chooseLength_rel : RelCT isa (AgreeRegs publicRegs) chooseLength
    (AgreeRegs (.rsi :: publicRegs)) :=
  RelCT.taintRegs (τ := Taint.ofRegs publicRegs)
    (fun _ _ hp => Taint.agree_ofRegs hp) (.rsi :: publicRegs) (by taint_decide)

theorem copy_rel : RelCT isa (AgreeRegs (.rax :: publicRegs)) copy (AgreeRegs publicRegs) :=
  RelCT.taintRegs (τ := Taint.ofRegs (.rax :: publicRegs))
    (fun _ _ hp => Taint.agree_ofRegs hp) publicRegs (by taint_decide)

theorem emitPrefix_rel : RelCT isa (AgreeRegs publicRegs) emitPrefix (AgreeRegs publicRegs) :=
  RelCT.taintRegs (τ := Taint.ofRegs publicRegs)
    (fun _ _ hp => Taint.agree_ofRegs hp) publicRegs (by taint_decide)

theorem copyRemaining_rel : RelCT isa (AgreeRegs publicRegs) copyRemaining (AgreeRegs publicRegs) :=
  RelCT.taintRegs (τ := Taint.ofRegs publicRegs)
    (fun _ _ hp => Taint.agree_ofRegs hp) publicRegs (by taint_decide)

theorem restore_rel : RelCT isa (AgreeRegs [.rbx]) (.block restore) fun _ _ => True :=
  RelCT.taint (A := taint) (Taint.ofRegs [.rbx]) (fun _ _ hp => Taint.agree_ofRegs hp)
    (by taint_decide)

end VG.Proof.Argon2.X86_64.HPrime
end

/-! # H′: retaining public caller state across hash calls -/

namespace VG.Proof.Argon2.X86_64.HPrime

open VG VG.X86_64 VG.Impl.Argon2.X86_64.HPrime

/-- Caller conditions that survive hashing in the workspace. -/
structure Stable (F : State → Prop) : Prop where
  ready : ∀ s, F s → FinalizeReady s
  keeps : ∀ s t, F s → Keeps s t → F t

def Related (F : State → Prop) (s t : State) : Prop := F s ∧ F t ∧ AgreeRegs publicRegs s t

theorem Related.keeps {F : State → Prop} (stable : Stable F) {s₁ s₂ t₁ t₂ : State}
    (h : Related F s₁ s₂) (k₁ : Keeps s₁ t₁) (k₂ : Keeps s₂ t₂) : Related F t₁ t₂ := by
  refine ⟨stable.keeps _ _ h.1 k₁, stable.keeps _ _ h.2.1 k₂, fun r hr => ?_⟩
  rw [k₁.regs _ (publicRegs_callee r hr), k₂.regs _ (publicRegs_callee r hr)]
  exact h.2.2 r hr

theorem keeps_rel {F : State → Prop} (stable : Stable F) {P : State → State → Prop} {c : Prog isa}
    (ct : RelCT isa P c fun _ _ => True)
    (wp : ∀ s₁ s₂, P s₁ s₂ → WP isa c s₁ (Keeps s₁) ∧ WP isa c s₂ (Keeps s₂))
    (pre : ∀ s₁ s₂, P s₁ s₂ → Related F s₁ s₂) : RelCT isa P c (Related F) :=
  (ct.wpDep wp).mono (fun _ _ h => h) fun _ _ ⟨_, _, _, hp, k₁, k₂⟩ =>
    (pre _ _ hp).keeps stable k₁ k₂

theorem stable_init_rel (v : Proof.Blake2.X86_64.Backend) {F : State → Prop} (stable : Stable F) :
    RelCT isa (fun s₁ s₂ => Related F s₁ s₂ ∧
      (1 ≤ (s₁.gpr .rsi).toNat ∧ (s₁.gpr .rsi).toNat ≤ 64) ∧ s₁.gpr .rsi = s₂.gpr .rsi)
      (init (hash v)) (Related F) := by
  have ready (s : State) (hs : F s) (len : 1 ≤ (s.gpr .rsi).toNat ∧ (s.gpr .rsi).toNat ≤ 64) :
      InitReady s := by
    have h := stable.ready s hs
    exact ⟨len, h.work, (h.stack.sub_left (below_sub (by decide) (by decide))).sub_right
      (Region.sub_prefix (by decide))⟩
  apply keeps_rel stable (init_rel v ?_) ?_ (fun _ _ h => h.1)
  · intro s₁ s₂ ⟨h, len, eq⟩
    exact ⟨ready s₁ h.1 len, ready s₂ h.2.1 (by rw [← eq]; exact len),
      h.2.2 _ (by decide), eq, h.2.2 _ (by decide)⟩
  · intro s₁ s₂ ⟨h, len, eq⟩
    exact ⟨init_keeps v s₁ (ready s₁ h.1 len),
      init_keeps v s₂ (ready s₂ h.2.1 (by rw [← eq]; exact len))⟩

theorem stable_finalize_rel (v : Proof.Blake2.X86_64.Backend) {F : State → Prop} (stable : Stable F) :
    RelCT isa (fun s₁ s₂ => Related F s₁ s₂ ∧ s₁.gpr .rsi = s₂.gpr .rsi)
      (finalize (hash v)) (Related F) := by
  apply keeps_rel stable (finalize_rel v ?_) ?_ (fun _ _ h => h.1)
  · intro s₁ s₂ ⟨h, count⟩
    exact ⟨stable.ready _ h.1, stable.ready _ h.2.1,
      h.2.2 _ (by decide), count, h.2.2 _ (by decide)⟩
  · intro s₁ s₂ ⟨h, _⟩
    exact ⟨finalize_keeps v s₁ (stable.ready _ h.1), finalize_keeps v s₂ (stable.ready _ h.2.1)⟩

end VG.Proof.Argon2.X86_64.HPrime
end

/-! # H′: constant time of hashing a fixed workspace buffer -/

namespace VG.Proof.Argon2.X86_64.HPrime

open VG VG.X86_64 VG.Impl.Argon2.X86_64.HPrime

theorem FixedArgs.keeps {s t : State} {offset size : Nat} (h : FixedArgs s t offset size) : Keeps s t := by
  refine ⟨fun r hr => ?_, h.rd, h.wr, ?_⟩
  · have hn : r ≠ .rsi ∧ r ≠ .rdx ∧ r ≠ .rcx := by
      simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    exact h.other r hn.1 hn.2.1 hn.2.2
  · rw [h.mem]; exact Frame.refl _ _

theorem fixed_ready {s t : State} {offset size : Nat} (ready : FinalizeReady s)
    (h : FixedArgs s t offset size) (lo : 768 ≤ offset) (hi : offset + size ≤ 16384) :
    UpdateReady t := by
  have k := h.keeps
  have len : (t.gpr .rcx).toNat = size := by
    rw [h.size, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  refine ⟨(ready.keeps k).work, ?_, ?_, ?_, (ready.keeps k).stack, ?_⟩
  · apply Covers.of_sub
    intro r hr
    simp only [List.mem_singleton] at hr; subst r
    refine ⟨⟨s.gpr .rbx, 16384⟩, List.mem_append_right _ (k.wr.symm ▸ ready.work), offset, h.data, ?_⟩
    change offset + (t.gpr .rcx).toNat ≤ 16384
    rw [len]; exact hi
  · rw [h.data, len, k.rbx]
    exact (Offset.base_disjoint _ (by omega) (by omega)).symm
  · rw [h.data, len, k.rbx]
    exact Offset.disjoint _ (d := offset) (n := size) (e := 192) (k := 576) (by omega) (by omega) (by decide)
  · rw [k.rsp, h.data, len]
    exact ready.stack.sub_right (Offset.sub_base _ hi)

theorem absorbFixed_keeps (v : Proof.Blake2.X86_64.Backend) (s : State) (offset size : Nat)
    (ready : FinalizeReady s) (lo : 768 ≤ offset) (hi : offset + size ≤ 16384) :
    WP isa (absorbFixed (hash v) offset size) s (Keeps s) := by
  unfold absorbFixed
  refine WP.seq ((fixedArgs_ok s offset size (by omega) (by omega)).mono fun u hu => ?_)
  exact (update_keeps v u (fixed_ready ready hu lo hi)).mono fun _ h => hu.keeps.trans h

theorem absorbFixed_rel (v : Proof.Blake2.X86_64.Backend) (offset size : Nat)
    (lo : 768 ≤ offset) (hi : offset + size ≤ 16384)
    (ct : ∃ hint, (taint.check (Taint.ofRegs []) (.block (fixedArgs offset size)) hint).isSome = true)
    {F : State → Prop} (stable : Stable F) :
    RelCT isa (Related F) (absorbFixed (hash v) offset size) (Related F) := by
  obtain ⟨_, ct⟩ := ct
  have args := (RelCT.taint (A := taint) (P := Related F) (Taint.ofRegs [])
    (fun _ _ _ => Taint.agree_ofRegs (by simp)) (c := .block (fixedArgs offset size))
    ct).wpDep (F := fun s t => FixedArgs s t offset size)
    fun s₁ s₂ _ => ⟨fixedArgs_ok s₁ offset size (by omega) (by omega),
      fixedArgs_ok s₂ offset size (by omega) (by omega)⟩
  have call := update_rel v (P := fun s₁ s₂ => True ∧
      ∃ σ₁ σ₂, Related F σ₁ σ₂ ∧ FixedArgs σ₁ s₁ offset size ∧ FixedArgs σ₂ s₂ offset size)
    fun s₁ s₂ ⟨_, σ₁, σ₂, hp, h₁, h₂⟩ => by
      have base := hp.2.2 .rbx (by decide)
      have sp := hp.2.2 .rsp (by decide)
      exact ⟨fixed_ready (stable.ready _ hp.1) h₁ lo hi, fixed_ready (stable.ready _ hp.2.1) h₂ lo hi,
        by rw [h₁.keeps.rbx, h₂.keeps.rbx, base], by rw [h₁.count, h₂.count],
        by rw [h₁.data, h₂.data, base], by rw [h₁.size, h₂.size], by rw [h₁.keeps.rsp, h₂.keeps.rsp, sp]⟩
  exact keeps_rel stable (args.seq call)
    (fun s₁ s₂ hp => ⟨absorbFixed_keeps v s₁ offset size (stable.ready _ hp.1) lo hi,
      absorbFixed_keeps v s₂ offset size (stable.ready _ hp.2.1) lo hi⟩) (fun _ _ h => h)

end VG.Proof.Argon2.X86_64.HPrime
