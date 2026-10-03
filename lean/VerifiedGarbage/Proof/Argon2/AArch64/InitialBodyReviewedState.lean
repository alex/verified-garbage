import VerifiedGarbage.Proof.Argon2.AArch64.InitialBodyState
import VerifiedGarbage.Proof.Argon2.References
import VerifiedGarbage.Proof.Argon2.AArch64.InitialBody
import VerifiedGarbage.Proof.Argon2.AArch64.InitFill
import VerifiedGarbage.Proof.Argon2.AArch64.FillFinish
import VerifiedGarbage.Proof.Argon2.AArch64.FillIterations
import VerifiedGarbage.Proof.Argon2.IterationsIndices
import VerifiedGarbage.Proof.Argon2.AArch64.FillIterationsBody
import VerifiedGarbage.Proof.Argon2.AArch64.FillIteration
import VerifiedGarbage.Proof.Argon2.AArch64.FillSlices
import VerifiedGarbage.Proof.Argon2.SlicesIndices
import VerifiedGarbage.Proof.Argon2.AArch64.FillSlicesBody
import VerifiedGarbage.Proof.Argon2.AArch64.FillSlice
import VerifiedGarbage.Proof.Argon2.AArch64.FillLanes
import VerifiedGarbage.Proof.Argon2.LanesIndices
import VerifiedGarbage.Proof.Argon2.AArch64.FillLanesBody
import VerifiedGarbage.Proof.Argon2.AArch64.SegmentSetupCT
import VerifiedGarbage.Proof.Argon2.AArch64.FinishReady
import VerifiedGarbage.Impl.Argon2.AArch64.Finish
import VerifiedGarbage.Proof.Argon2.AArch64.FinalOutputReady
import VerifiedGarbage.Proof.Argon2.AArch64.FinalCall
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Argon2.AArch64.Initial
import VerifiedGarbage.Proof.Argon2.AArch64.HPrime.FixedCT
import VerifiedGarbage.Proof.Argon2.AArch64.InitialLit
import VerifiedGarbage.Proof.Framework.AArch64.RelCT

/-! Merged from `Proof.Argon2.AArch64.InitialCTState`. -/
section
/-! Merged from `Proof.Argon2.AArch64.InitialBlocksCT`. -/
section
/-! # Constant time of H₀ header and input argument preparation

Only frame and scratch addresses affect these blocks' execution traces.
The relational proof of the complete derivation additionally tracks public
lengths and pointers across its BLAKE2b calls.
-/

namespace VG.Proof.Argon2.AArch64.Initial

open VG VG.AArch64 VG.Impl.Argon2.AArch64.Initial

def AgreeBases (s t : State) : Prop := s.sp = t.sp ∧ s.gpr .x19 = t.gpr .x19 ∧ s.gpr .x24 = t.gpr .x24

theorem agreeBases_taint {s t : State} (h : AgreeBases s t) :
    VG.AArch64.Taint.Agree (Taint.ofRegs [.x19, .x24]) s t := by
  refine ⟨h.1, ?_⟩
  intro r hr
  simp only [Taint.ofRegs, RegSet.mem_ofList, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact h.2.1
  · exact h.2.2

theorem header_rel : RelCT isa AgreeBases headerCode (fun _ _ => True) :=
  RelCT.taint (A := taint) (Taint.ofRegs [.x19, .x24])
    (fun _ _ h => agreeBases_taint h) (by taint_decide)

theorem lengthArgs_rel (offset : Nat)
    (ct : ∃ hint, (taint.check (Taint.ofRegs [.x19, .x24])
      (.block (lengthArgs offset)) hint).isSome = true) :
    RelCT isa AgreeBases (.block (lengthArgs offset)) (fun _ _ => True) := by
  obtain ⟨_, check⟩ := ct
  exact RelCT.taint (A := taint) (Taint.ofRegs [.x19, .x24])
    (fun _ _ h => agreeBases_taint h) check

theorem inputArgs_rel (offset : Nat)
    (ct : ∃ hint, (taint.check (Taint.ofRegs [.x19])
      (.block (inputArgs offset)) hint).isSome = true) :
    RelCT isa (fun s t => s.sp = t.sp ∧ s.gpr .x19 = t.gpr .x19)
      (.block (inputArgs offset)) (fun _ _ => True) := by
  obtain ⟨_, check⟩ := ct
  exact RelCT.taint (A := taint) (Taint.ofRegs [.x19])
    (fun _ _ h => ⟨h.1, by
      intro r hr; simp only [Taint.ofRegs, RegSet.mem_ofList, List.mem_singleton] at hr; subst r; exact h.2⟩) check

/-- All four concrete input blocks use their checked public base address. -/
theorem inputs_rel :
    RelCT isa AgreeBases (.block (lengthArgs passwordLenOffset)) (fun _ _ => True) ∧
    RelCT isa AgreeBases (.block (lengthArgs saltLenOffset)) (fun _ _ => True) ∧
    RelCT isa AgreeBases (.block (lengthArgs secretLenOffset)) (fun _ _ => True) ∧
    RelCT isa AgreeBases (.block (lengthArgs adLenOffset)) (fun _ _ => True) ∧
    RelCT isa (fun s t => s.sp = t.sp ∧ s.gpr .x19 = t.gpr .x19)
      (.block (inputArgs passwordOffset)) (fun _ _ => True) ∧
    RelCT isa (fun s t => s.sp = t.sp ∧ s.gpr .x19 = t.gpr .x19)
      (.block (inputArgs saltOffset)) (fun _ _ => True) ∧
    RelCT isa (fun s t => s.sp = t.sp ∧ s.gpr .x19 = t.gpr .x19)
      (.block (inputArgs secretOffset)) (fun _ _ => True) ∧
    RelCT isa (fun s t => s.sp = t.sp ∧ s.gpr .x19 = t.gpr .x19)
      (.block (inputArgs adOffset)) (fun _ _ => True) :=
  ⟨lengthArgs_rel _ ⟨_, by taint_decide⟩, lengthArgs_rel _ ⟨_, by taint_decide⟩,
    lengthArgs_rel _ ⟨_, by taint_decide⟩, lengthArgs_rel _ ⟨_, by taint_decide⟩,
    inputArgs_rel _ ⟨_, by taint_decide⟩, inputArgs_rel _ ⟨_, by taint_decide⟩,
    inputArgs_rel _ ⟨_, by taint_decide⟩, inputArgs_rel _ ⟨_, by taint_decide⟩⟩

end VG.Proof.Argon2.AArch64.Initial
end

/-! Public input metadata survives every hash call without relating input bytes. -/

namespace VG.Proof.Argon2.AArch64.Initial

open VG VG.AArch64

structure Ready (s : State) : Prop where
  space : Space s
  inputs : ∀ input ∈ inputs, InputReady s input.1 input.2

theorem Ready.keeps {s t : State} (h : Ready s) (k : Keeps s t) : Ready t :=
  ⟨h.space.keeps k, fun p hp => (h.inputs p hp).keeps k⟩

structure Related (s t : State) : Prop where
  left : Ready s
  right : Ready t
  bp : s.gpr .x19 = t.gpr .x19
  bx : s.gpr .x24 = t.gpr .x24
  sp : s.sp = t.sp
  words : ∀ d ∈ slots, wordAt s d = wordAt t d

theorem Related.keeps {s₁ s₂ t₁ t₂ : State} (h : Related s₁ s₂)
    (k₁ : Keeps s₁ t₁) (k₂ : Keeps s₂ t₂) : Related t₁ t₂ := by
  refine ⟨h.left.keeps k₁, h.right.keeps k₂, ?_, ?_, ?_, ?_⟩
  · rw [k₁.x19, k₂.x19, h.bp]
  · rw [k₁.x24, k₂.x24, h.bx]
  · rw [k₁.sp, k₂.sp, h.sp]
  · intro d hd
    have bound : ∀ d ∈ slots, d + 8 ≤ 272 := by decide
    rw [h.left.space.word_keeps k₁ d (bound d hd), h.right.space.word_keeps k₂ d (bound d hd)]
    exact h.words d hd

def RelatedRegs (rs : List Reg) (s t : State) : Prop :=
  Related s t ∧ ∀ r ∈ rs, s.gpr r = t.gpr r

theorem hash_keeps_rel {P : State → State → Prop} {c : Prog isa} (rs : List Reg)
    (saved : ∀ r ∈ rs, r ∈ preserved ∧ r ≠ .x30)
    (ct : RelCT isa P c (fun _ _ => True))
    (pre : ∀ s t, P s t → RelatedRegs rs s t)
    (wp : ∀ s t, P s t → WP isa c s (HPrime.Keeps s) ∧ WP isa c t (HPrime.Keeps t)) :
    RelCT isa P c (RelatedRegs rs) := by
  apply (ct.wpDep wp).mono (fun _ _ h => h)
  rintro a b ⟨_, s, t, hp, ha, hb⟩
  have h := pre s t hp
  refine ⟨h.1.keeps (Keeps.of_hash ha) (Keeps.of_hash hb), ?_⟩
  intro r hr
  rw [ha.regs r (saved r hr).1 (saved r hr).2, hb.regs r (saved r hr).1 (saved r hr).2]
  exact h.2 r hr

theorem finalize_ready {s : State} (h : Ready s) : HPrime.FinalizeReady s :=
  ⟨h.space.stackMinimum, h.space.work, h.space.stackWork⟩

end VG.Proof.Argon2.AArch64.Initial
end

/-! Merged from `Proof.Argon2.AArch64.InitialUpdateReady`. -/
section
/-! Permissions for the two updates of each length-prefixed H₀ input. -/

namespace VG.Proof.Argon2.AArch64.Initial

open VG VG.AArch64

theorem prefix_update_ready {s t : State} {lo : Nat} (h : Space s) (args : LengthArgs s lo t) :
    HPrime.UpdateReady t := by
  have k := args.keeps
  have ht := h.keeps k
  have len : (t.gpr .x3).toNat = 4 := by rw [args.size]; rfl
  refine ⟨ht.stackMinimum, ht.work, ?_, ?_, ?_, ht.stackWork, ?_⟩
  · rw [args.pointer, len, ← k.x24]
    apply Covers.of_sub
    intro r hr
    simp only [List.mem_singleton] at hr; subst r
    exact ⟨⟨t.gpr .x24, 16384⟩, List.mem_append_right _ ht.work, 792, rfl, by change 792 + 4 ≤ 16384; decide⟩
  · rw [args.pointer, len, k.x24]
    exact (Offset.base_disjoint _ (by decide) (by decide)).symm
  · rw [args.pointer, len, k.x24]
    exact Offset.disjoint _ (d := 792) (n := 4) (e := 192) (k := 576) (by decide) (by decide) (by decide)
  · rw [args.pointer, len, ← k.x24]
    exact ht.stackWork.sub_right (Offset.sub_base _ (by decide))

theorem input_update_ready {s t : State} {po lo : Nat} (h : InputReady s po lo)
    (length : s.gpr .x22 = wordAt s lo) (args : InputArgs s t po) : HPrime.UpdateReady t := by
  have k := args.keeps
  have ptr : t.gpr .x2 = wordAt s po := args.pointer
  have len : t.gpr .x3 = wordAt s lo := args.length.trans length
  refine ⟨(h.space.keeps k).stackMinimum, (h.space.keeps k).work, ?_, ?_, ?_, (h.space.keeps k).stackWork, ?_⟩
  · rw [ptr, len, k.rd, k.wr]; exact h.cover
  · rw [ptr, len, k.x24]; exact h.work.sub_right (Region.sub_prefix (by decide))
  · rw [ptr, len, k.x24]; exact h.work.sub_right (Offset.sub_base _ (by decide))
  · rw [ptr, len, k.sp]; exact h.stack.symm

structure LengthRelated (lo : Nat) (s t : State) : Prop where
  related : RelatedRegs [.x20, .x22] s t
  leftLength : s.gpr .x22 = wordAt s lo
  rightLength : t.gpr .x22 = wordAt t lo

theorem LengthRelated.hash_keeps {lo : Nat} {s t a b : State} (h : LengthRelated lo s t)
    (bound : lo + 8 ≤ 272) (ka : HPrime.Keeps s a) (kb : HPrime.Keeps t b) : LengthRelated lo a b := by
  refine ⟨⟨h.related.1.keeps (Keeps.of_hash ka) (Keeps.of_hash kb), ?_⟩, ?_, ?_⟩
  · intro r hr
    have saved : ∀ r ∈ ([.x20, .x22] : List Reg), r ∈ preserved ∧ r ≠ .x30 := by decide
    rw [ka.regs r ((saved r hr).1) ((saved r hr).2), kb.regs r ((saved r hr).1) ((saved r hr).2)]
    exact h.related.2 r hr
  · rw [ka.regs .x22 (by decide) (by decide), h.related.1.left.space.word_keeps (Keeps.of_hash ka) lo bound]
    exact h.leftLength
  · rw [kb.regs .x22 (by decide) (by decide), h.related.1.right.space.word_keeps (Keeps.of_hash kb) lo bound]
    exact h.rightLength

end VG.Proof.Argon2.AArch64.Initial
end

/-! Merged from `Proof.Argon2.AArch64.InitialStartCT`. -/
section
/-! H₀ initialization and its fixed parameter header have input-independent traces. -/

namespace VG.Proof.Argon2.AArch64.Initial

open VG VG.AArch64 VG.Impl.Argon2.AArch64.Initial

theorem digestLength_rel : RelCT isa Related (.block ([Impl.Argon2.AArch64.Instructions.imm .x1 64].flatten))
    (fun s t => Related s t ∧ s.gpr .x1 = 64 ∧ t.gpr .x1 = 64) := by
  have ct := (RelCT.taint (A := taint) (P := Related) (Taint.ofRegs [])
    (fun _ _ hp => ⟨hp.sp, by simp [Taint.ofRegs]⟩)
    (c := .block ([Impl.Argon2.AArch64.Instructions.imm .x1 64].flatten)) (by taint_decide)).wpDep
    (fun s t _ => ⟨digestLength_ok s, digestLength_ok t⟩)
  apply ct.mono (fun _ _ h => h)
  rintro a b ⟨_, s, t, hp, ⟨la, _, ka⟩, ⟨lb, _, kb⟩⟩
  exact ⟨hp.keeps (Keeps.of_hash ka) (Keeps.of_hash kb), la, lb⟩

theorem init_hash_rel (v : HPrime.Backend) :
    RelCT isa (fun s t => Related s t ∧ s.gpr .x1 = 64 ∧ t.gpr .x1 = 64)
      (Impl.Argon2.AArch64.HPrime.init v.hash) Related := by
  have ready (s : State) (h : Ready s) (len : s.gpr .x1 = 64) : HPrime.InitReady s :=
    ⟨by rw [len]; decide, h.space.work,
      (h.space.stackWork.sub_left (below_sub (by decide) (by decide))).sub_right (Region.sub_prefix (by decide))⟩
  have ct := HPrime.init_rel v (P := fun s t => Related s t ∧ s.gpr .x1 = 64 ∧ t.gpr .x1 = 64)
    (fun s t ⟨h, ls, lt⟩ => ⟨ready s h.left ls, ready t h.right lt,
      h.bx, ls.trans lt.symm, h.sp⟩)
  have result := hash_keeps_rel [] (by simp) ct (fun _ _ h => ⟨h.1, by simp⟩)
    (fun s t ⟨h, ls, lt⟩ => ⟨HPrime.init_keeps v s (ready s h.left ls), HPrime.init_keeps v t (ready t h.right lt)⟩)
  exact result.mono (fun _ _ h => h) (fun _ _ h => h.1)

theorem header_state_rel : RelCT isa Related headerCode Related := by
  have ct := (header_rel.mono (P' := Related) (fun _ _ h => ⟨h.sp, h.bp, h.bx⟩)
    (fun _ _ h => h)).wpDep (fun s t h =>
      ⟨headerWords_ok s 6 (by decide) h.left.space, headerWords_ok t 6 (by decide) h.right.space⟩)
  exact ct.mono (fun _ _ h => h) (fun _ _ ⟨_, _, _, hp, ⟨_, ka⟩, ⟨_, kb⟩⟩ => hp.keeps ka kb)

theorem fixed_header_rel (v : HPrime.Backend) :
    RelCT isa Related (Impl.Argon2.AArch64.HPrime.absorbFixed v.hash 768 24) Related := by
  have args := (RelCT.taint (A := taint) (P := Related) (Taint.ofRegs [])
    (fun _ _ hp => ⟨hp.sp, by simp [Taint.ofRegs]⟩)
    (c := .block (Impl.Argon2.AArch64.HPrime.fixedArgs 768 24)) (by taint_decide)).wpDep
    (fun s t _ => ⟨HPrime.fixedArgs_ok s 768 24 (by decide) (by decide),
      HPrime.fixedArgs_ok t 768 24 (by decide) (by decide)⟩)
  have call := HPrime.update_rel v (P := fun a b => True ∧ ∃ s t, Related s t ∧
      HPrime.FixedArgs s a 768 24 ∧ HPrime.FixedArgs t b 768 24)
    (fun a b ⟨_, s, t, hp, ha, hb⟩ => ⟨HPrime.fixed_ready (finalize_ready hp.left) ha (by decide) (by decide),
      HPrime.fixed_ready (finalize_ready hp.right) hb (by decide) (by decide),
      by rw [ha.keeps.x24, hb.keeps.x24, hp.bx], by rw [ha.count, hb.count],
      by rw [ha.data, hb.data, hp.bx], by rw [ha.size, hb.size], by rw [ha.keeps.sp, hb.keeps.sp, hp.sp]⟩)
  have ct := args.seq call
  have result := hash_keeps_rel [] (by simp) ct (fun _ _ h => ⟨h, by simp⟩)
    (fun s t h => ⟨HPrime.absorbFixed_keeps v s 768 24 (finalize_ready h.left) (by decide) (by decide) (by decide),
      HPrime.absorbFixed_keeps v t 768 24 (finalize_ready h.right) (by decide) (by decide) (by decide)⟩)
  exact result.mono (fun _ _ h => h) (fun _ _ h => h.1)

theorem initialCount_rel : RelCT isa Related (.block ([Impl.Argon2.AArch64.Instructions.imm .x20 24].flatten)) (RelatedRegs [.x20]) := by
  have ct := (RelCT.taint (A := taint) (P := Related) (Taint.ofRegs [])
    (fun _ _ hp => ⟨hp.sp, by simp [Taint.ofRegs]⟩)
    (c := .block ([Impl.Argon2.AArch64.Instructions.imm .x20 24].flatten)) (by taint_decide)).wpDep
    (fun s t _ => ⟨initialCount_ok s, initialCount_ok t⟩)
  apply ct.mono (fun _ _ h => h)
  rintro a b ⟨_, s, t, hp, ⟨la, _, ka⟩, ⟨lb, _, kb⟩⟩
  refine ⟨hp.keeps ka kb, ?_⟩
  intro r hr
  simp only [List.mem_singleton] at hr; subst r
  exact la.trans lb.symm

theorem start_rel (v : HPrime.Backend) :
    RelCT isa Related (start v.hash) (RelatedRegs [.x20]) :=
  digestLength_rel.seq ((init_hash_rel v).seq (header_state_rel.seq
    ((fixed_header_rel v).seq initialCount_rel)))

end VG.Proof.Argon2.AArch64.Initial
end

/-! Merged from `Proof.Argon2.AArch64.InitialFinishCT`. -/
section
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
end

/-! Merged from `Proof.Argon2.AArch64.InitialCT`. -/
section
/-! Merged from `Proof.Argon2.AArch64.InitialAbsorbCT`. -/
section
/-! H₀ updates depend on public lengths and pointers, never on input contents. -/

namespace VG.Proof.Argon2.AArch64.Initial

open VG VG.AArch64 VG.Impl.Argon2.AArch64.Initial

def PrefixRelated (lo : Nat) (a b : State) : Prop :=
  True ∧ ∃ s t, RelatedRegs [.x20] s t ∧ LengthArgs s lo a ∧ LengthArgs t lo b

theorem prefix_rel (v : HPrime.Backend) (lo : Nat) (slot : lo ∈ slots)
    (bound : lo + 8 ≤ 272)
    (check : ∃ hint, (taint.check (Taint.ofRegs [.x19, .x24]) (.block (lengthArgs lo)) hint).isSome = true) :
    RelCT isa (RelatedRegs [.x20])
      (.seq (.block (lengthArgs lo)) (Impl.Argon2.AArch64.HPrime.update v.hash)) (LengthRelated lo) := by
  have args := ((lengthArgs_rel lo check).mono (P' := RelatedRegs [.x20])
    (fun _ _ h => ⟨h.1.sp, h.1.bp, h.1.bx⟩) (fun _ _ h => h)).wpDep
    (fun s t h => ⟨lengthArgs_ok s lo (slots_aligned lo slot) (by omega) (h.1.left.space.readable lo slot)
      (by simpa using h.1.left.space.write 792 4 (by decide)),
      lengthArgs_ok t lo (slots_aligned lo slot) (by omega) (h.1.right.space.readable lo slot)
      (by simpa using h.1.right.space.write 792 4 (by decide))⟩)
  have call := HPrime.update_rel v (P := PrefixRelated lo) (fun a b ⟨_, s, t, hp, ha, hb⟩ =>
    ⟨prefix_update_ready hp.1.left.space ha, prefix_update_ready hp.1.right.space hb,
      by rw [ha.keeps.x24, hb.keeps.x24, hp.1.bx], by rw [ha.count, hb.count]; exact hp.2 _ (by simp),
      by rw [ha.pointer, hb.pointer, hp.1.bx], by rw [ha.size, hb.size],
      by rw [ha.keeps.sp, hb.keeps.sp, hp.1.sp]⟩)
  have called := call.wpDep (fun a b ⟨_, s, t, hp, ha, hb⟩ =>
    ⟨HPrime.update_keeps v a (prefix_update_ready hp.1.left.space ha),
      HPrime.update_keeps v b (prefix_update_ready hp.1.right.space hb)⟩)
  have finished := called.mono (fun _ _ h => h) (fun a b h => by
    obtain ⟨_, x, y, ⟨_, s, t, hp, ha, hb⟩, ka, kb⟩ := h
    have rel := hp.1.keeps ha.keeps hb.keeps
    have prepared : LengthRelated lo x y := by
      refine ⟨⟨rel, ?_⟩, ?_, ?_⟩
      · intro r hr
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · rw [ha.other _ (by decide),
            hb.other _ (by decide)]
          exact hp.2 _ (by simp)
        · rw [ha.length, hb.length]; exact hp.1.words lo slot
      · rw [hp.1.left.space.word_keeps ha.keeps lo bound]; exact ha.length
      · rw [hp.1.right.space.word_keeps hb.keeps lo bound]; exact hb.length
    exact prepared.hash_keeps bound ka kb)
  exact args.seq finished

def InputRelated (lo po : Nat) (a b : State) : Prop :=
  True ∧ ∃ s t, LengthRelated lo s t ∧ InputArgs s a po ∧ InputArgs t b po

theorem input_rel (v : HPrime.Backend) (po lo : Nat) (input : (po, lo) ∈ inputs)
    (check : ∃ hint, (taint.check (Taint.ofRegs [.x19]) (.block (inputArgs po)) hint).isSome = true) :
    RelCT isa (LengthRelated lo)
      (.seq (.block (inputArgs po)) (Impl.Argon2.AArch64.HPrime.update v.hash)) (LengthRelated lo) := by
  have args := ((inputArgs_rel po check).mono (P' := LengthRelated lo)
    (fun _ _ h => ⟨h.related.1.sp, h.related.1.bp⟩) (fun _ _ h => h)).wpDep
    (fun s t h => ⟨inputArgs_ok s po (slots_aligned po (h.related.1.left.inputs _ input).pointerSlot) (by have := (h.related.1.left.inputs _ input).pointerBound; omega) (h.related.1.left.space.readable po (h.related.1.left.inputs _ input).pointerSlot),
      inputArgs_ok t po (slots_aligned po (h.related.1.right.inputs _ input).pointerSlot) (by have := (h.related.1.right.inputs _ input).pointerBound; omega) (h.related.1.right.space.readable po (h.related.1.right.inputs _ input).pointerSlot)⟩)
  have call := HPrime.update_rel v (P := InputRelated lo po) (fun a b ⟨_, s, t, hp, ha, hb⟩ =>
    ⟨input_update_ready (hp.related.1.left.inputs _ input) hp.leftLength ha,
      input_update_ready (hp.related.1.right.inputs _ input) hp.rightLength hb,
      by rw [ha.keeps.x24, hb.keeps.x24, hp.related.1.bx],
      by rw [ha.count, hb.count, hp.related.2 .x20 (by simp)],
      by rw [ha.pointer, hb.pointer]; exact hp.related.1.words po (hp.related.1.left.inputs _ input).pointerSlot,
      by rw [ha.length, hb.length]; exact hp.related.2 .x22 (by simp),
      by rw [ha.keeps.sp, hb.keeps.sp, hp.related.1.sp]⟩)
  have called := call.wpDep (fun a b ⟨_, s, t, hp, ha, hb⟩ =>
    ⟨HPrime.update_keeps v a (input_update_ready (hp.related.1.left.inputs _ input) hp.leftLength ha),
      HPrime.update_keeps v b (input_update_ready (hp.related.1.right.inputs _ input) hp.rightLength hb)⟩)
  have finished := called.mono (fun _ _ h => h) (fun a b h => by
    obtain ⟨_, x, y, ⟨_, s, t, hp, ha, hb⟩, ka, kb⟩ := h
    have left := hp.related.1.left.inputs _ input
    have right := hp.related.1.right.inputs _ input
    have prepared : LengthRelated lo x y := by
      refine ⟨⟨hp.related.1.keeps ha.keeps hb.keeps, ?_⟩, ?_, ?_⟩
      · intro r hr
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · rw [ha.total, hb.total, hp.related.2 .x20 (by simp)]
        · rw [ha.other _ (by decide),
            hb.other _ (by decide)]
          exact hp.related.2 .x22 (by simp)
      · rw [left.space.word_keeps ha.keeps lo left.lengthBound,
          ha.other _ (by decide)]
        exact hp.leftLength
      · rw [right.space.word_keeps hb.keeps lo right.lengthBound,
          hb.other _ (by decide)]
        exact hp.rightLength
    exact prepared.hash_keeps left.lengthBound ka kb)
  exact args.seq finished

theorem addCount_rel (lo : Nat) :
    RelCT isa (LengthRelated lo) (.block (Impl.Argon2.AArch64.Instructions.add .x20 .x22)) (RelatedRegs [.x20]) := by
  have ct := (RelCT.taint (A := taint) (P := LengthRelated lo) (Taint.ofRegs [])
    (fun _ _ hp => ⟨hp.related.1.sp, by simp [Taint.ofRegs]⟩)
    (c := .block (Impl.Argon2.AArch64.Instructions.add .x20 .x22)) (by taint_decide)).wpDep
    (fun s t _ => ⟨addCount_ok s, addCount_ok t⟩)
  apply ct.mono (fun _ _ h => h)
  rintro a b ⟨_, s, t, hp, ⟨ca, _, ka⟩, ⟨cb, _, kb⟩⟩
  refine ⟨hp.related.1.keeps ka kb, ?_⟩
  intro r hr
  simp only [List.mem_singleton] at hr; subst r
  rw [ca, cb, hp.related.2 .x20 (by simp), hp.related.2 .x22 (by simp)]

theorem absorb_rel (v : HPrime.Backend) (po lo : Nat) (input : (po, lo) ∈ inputs)
    (lengthCheck : ∃ hint, (taint.check (Taint.ofRegs [.x19, .x24]) (.block (lengthArgs lo)) hint).isSome = true)
    (pointerCheck : ∃ hint, (taint.check (Taint.ofRegs [.x19]) (.block (inputArgs po)) hint).isSome = true) :
    RelCT isa (RelatedRegs [.x20]) (absorb v.hash po lo) (RelatedRegs [.x20]) := by
  have slot : lo ∈ slots := by
    have all : ∀ p ∈ inputs, p.2 ∈ slots := by decide
    exact all _ input
  have bound : lo + 8 ≤ 272 := by
    have all : ∀ d ∈ slots, d + 8 ≤ 272 := by decide
    exact all lo slot
  exact ((prefix_rel v lo slot bound lengthCheck).seq
    (((input_rel v po lo input pointerCheck).seq (addCount_rel lo)).assoc)).assoc

end VG.Proof.Argon2.AArch64.Initial
end

/-! Complete H₀ is constant time for every verified BLAKE2b backend. -/

namespace VG.Proof.Argon2.AArch64.Initial

open VG VG.AArch64 VG.Impl.Argon2.AArch64.Initial

theorem code_rel (v : HPrime.Backend) :
    RelCT isa Related (code v.hash) (fun _ _ => True) :=
  (start_rel v).seq
    ((absorb_rel v passwordOffset passwordLenOffset (by decide) ⟨_, by taint_decide⟩ ⟨_, by taint_decide⟩).seq
    ((absorb_rel v saltOffset saltLenOffset (by decide) ⟨_, by taint_decide⟩ ⟨_, by taint_decide⟩).seq
    ((absorb_rel v secretOffset secretLenOffset (by decide) ⟨_, by taint_decide⟩ ⟨_, by taint_decide⟩).seq
    ((absorb_rel v adOffset adLenOffset (by decide) ⟨_, by taint_decide⟩ ⟨_, by taint_decide⟩).seq
      (finish_rel v)))))

end VG.Proof.Argon2.AArch64.Initial
end

/-! Merged from `Proof.Argon2.AArch64.InitialBodyReviewedCT`. -/
section
/-! Merged from `Proof.Argon2.AArch64.InitialBodyCT`. -/
section
/-! Merged from `Proof.Argon2.AArch64.InitFillCT`. -/
section
/-! Merged from `Proof.Argon2.AArch64.FinishStageCT`. -/
section
/-! Merged from `Proof.Argon2.AArch64.FinalOutputCT`. -/
section
/-! Merged from `Proof.Argon2.AArch64.FinalCallCT`. -/
section
/-! # The final H′ call leak only their public argument registers -/

namespace VG.Proof.Argon2.AArch64.FinalCall

open VG VG.AArch64
open VG.Impl.Argon2.AArch64.HPrime (code)

theorem hPrime_call_rel (v : HPrime.Backend) (name : String) (len : Nat)
    {P : State → State → Prop}
    (pre : ∀ s t, P s t → CallReady len s ∧ CallReady len t ∧
      s.gpr .x1 = 1024 ∧ t.gpr .x1 = 1024 ∧ s.gpr .x3 = BitVec.ofNat 64 len ∧ t.gpr .x3 = BitVec.ofNat 64 len ∧
      s.gpr .x0 = t.gpr .x0 ∧ s.gpr .x2 = t.gpr .x2 ∧
      s.gpr .x4 = t.gpr .x4 ∧ s.sp = t.sp) :
    RelCT isa P (.call name (code v.hash)) (fun _ _ => True) := by
  apply RelCT.callEx (k := HPrime.localContract) (HPrime.code_correct v) (HPrime.code_ct v)
  intro s t hp
  obtain ⟨hs, ht, ls, lt, os, ot, di, dx, x4, sp⟩ := pre s t hp
  obtain ⟨ps, cs, ws⟩ := hPrime_call_hyps len s hs ls os
  obtain ⟨pt, ct, wt⟩ := hPrime_call_hyps len t ht lt ot
  refine ⟨_, _, _, _, ps, pt, ?_, cs, ws, ct, wt⟩
  change s.callEntry.gpr .x0 = t.callEntry.gpr .x0 ∧
    s.callEntry.gpr .x1 = t.callEntry.gpr .x1 ∧
    s.callEntry.gpr .x2 = t.callEntry.gpr .x2 ∧
    s.callEntry.gpr .x3 = t.callEntry.gpr .x3 ∧
    s.callEntry.gpr .x4 = t.callEntry.gpr .x4 ∧
    s.callEntry.sp = t.callEntry.sp
  simp only [State.callEntry_gpr _ (by decide : Reg.x0 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.x1 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.x2 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.x3 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.x4 ∉ linkRegs), State.callEntry_sp]
  exact ⟨di, ls.trans lt.symm, dx, os.trans ot.symm, x4, sp⟩

end VG.Proof.Argon2.AArch64.FinalCall
end

/-! Final hashing exposes only the public tag length and pointers, for any hash backend. -/

namespace VG.Proof.Argon2.AArch64.FinalOutput

open VG VG.AArch64 VG.Spec.Argon2

structure Related (p : Params) (s t : State) : Prop where
  left : Ready p s
  right : Ready p t
  bases : s.gpr .x19 = t.gpr .x19
  stacks : s.sp = t.sp
  matrices : ReductionState.matrix s = ReductionState.matrix t
  outputs : output s = output t
  works : work s = work t

structure NextRelated (p : Params) (s t : State) : Prop where
  left : FinalCall.CallReady p.tagLen s
  right : FinalCall.CallReady p.tagLen t
  leftInputLength : s.gpr .x1 = 1024
  rightInputLength : t.gpr .x1 = 1024
  leftOutputLength : s.gpr .x3 = BitVec.ofNat 64 p.tagLen
  rightOutputLength : t.gpr .x3 = BitVec.ofNat 64 p.tagLen
  inputs : s.gpr .x0 = t.gpr .x0
  outputs : s.gpr .x2 = t.gpr .x2
  works : s.gpr .x4 = t.gpr .x4
  stacks : s.sp = t.sp

theorem args_trace : RelCT isa (fun s t => s.gpr .x19 = t.gpr .x19 ∧ s.sp = t.sp)
    (.block Impl.Argon2.AArch64.FinalOutput.args) (fun _ _ => True) :=
  (RelCT.taintRegs (τ := Taint.ofRegs [.x19])
    (fun _ _ h => ⟨h.2, by
      intro r hr; simp only [Taint.mem_ofRegs, List.mem_singleton] at hr; subst r; exact h.1⟩)
    [] (by taint_decide)).mono (fun _ _ h => h) (fun _ _ _ => trivial)

theorem args_rel (p : Params) : RelCT isa (Related p)
    (.block Impl.Argon2.AArch64.FinalOutput.args) (NextRelated p) := by
  have trace := args_trace.mono (P' := Related p) (fun _ _ h => ⟨h.bases, h.stacks⟩) (fun _ _ h => h)
  have full := trace.wpDep (fun s t h => ⟨args_ok s h.left.reads, args_ok t h.right.reads⟩)
  refine full.mono (fun _ _ h => h) ?_
  intro a b h
  obtain ⟨_, s, t, hp, ha, hb⟩ := h
  exact ⟨ha.ready hp.left, hb.ready hp.right, ha.inputLength, hb.inputLength,
    ha.outputLength.trans hp.left.tagWord, hb.outputLength.trans hp.right.tagWord,
    ha.input.trans (hp.matrices.trans hb.input.symm), ha.output.trans (hp.outputs.trans hb.output.symm),
    ha.work.trans (hp.works.trans hb.work.symm),
    (ha.keeps.sp).trans (hp.stacks.trans (hb.keeps.sp).symm)⟩

theorem code_rel (v : HPrime.Backend) (name : String) (p : Params) :
    RelCT isa (Related p) (Impl.Argon2.AArch64.FinalOutput.code name v.hash) (fun _ _ => True) :=
  (args_rel p).seq (FinalCall.hPrime_call_rel v name p.tagLen (fun _ _ h =>
    ⟨h.left, h.right, h.leftInputLength, h.rightInputLength, h.leftOutputLength, h.rightOutputLength,
      h.inputs, h.outputs, h.works, h.stacks⟩))

end VG.Proof.Argon2.AArch64.FinalOutput
end

/-! Complete finalization has a public trace for every BLAKE2b backend. -/

namespace VG.Proof.Argon2.AArch64.Finish

open VG VG.AArch64 VG.Spec.Argon2 ReductionState

structure Related (p : Params) (leftMemory rightMemory : Array Block) (s t : State) : Prop where
  left : Ready p s
  right : Ready p t
  bases : s.gpr .x19 = t.gpr .x19
  stacks : s.sp = t.sp
  matrices : matrix s = matrix t
  outputs : FinalOutput.output s = FinalOutput.output t
  works : FinalOutput.work s = FinalOutput.work t
  leftMatrix : Proof.Argon2.Represents s.mem (matrix s) p.blocks leftMemory
  rightMatrix : Proof.Argon2.Represents t.mem (matrix t) p.blocks rightMemory

theorem code_rel (v : HPrime.Backend) (name : String) (p : Params)
    (leftMemory rightMemory : Array Block) :
    RelCT isa (Related p leftMemory rightMemory) (Impl.Argon2.AArch64.Finish.code name v.hash)
      (fun _ _ => True) := by
  intro s t ts tt a b hp ea eb
  cases ea with
  | seq reduceA outputA =>
    cases eb with
    | seq reduceB outputB =>
      have related : ReductionInit.Related p leftMemory rightMemory s t :=
        ⟨hp.left.reduction, hp.right.reduction, hp.bases, hp.stacks, hp.matrices, hp.leftMatrix, hp.rightMatrix⟩
      obtain ⟨reduceTrace, _⟩ := FinalReduction.code_rel p hp.left.reduction.allocation.positive
        leftMemory rightMemory _ _ _ _ _ _ related reduceA reduceB
      obtain ⟨_, sa, runA, doneA⟩ := FinalReduction.code_ok s p hp.left.reduction leftMemory hp.leftMatrix
      obtain ⟨_, sb, runB, doneB⟩ := FinalReduction.code_ok t p hp.right.reduction rightMemory hp.rightMatrix
      obtain ⟨_, rfl⟩ := Exec.det reduceA runA
      obtain ⟨_, rfl⟩ := Exec.det reduceB runB
      have finalRelated : FinalOutput.Related p _ _ :=
        ⟨output_ready hp.left doneA, output_ready hp.right doneB,
          (doneA.regs .x19 (by simp [FillCompress.loopRegs]) (by decide)).trans
            (hp.bases.trans (doneB.regs .x19 (by simp [FillCompress.loopRegs]) (by decide)).symm),
          (doneA.sp).trans
            (hp.stacks.trans (doneB.sp).symm),
          doneA.base.trans (hp.matrices.trans doneB.base.symm),
          (frame_word hp.left.reduction doneA 256 (by decide)).trans
            (hp.outputs.trans (frame_word hp.right.reduction doneB 256 (by decide)).symm),
          (frame_word hp.left.reduction doneA 248 (by decide)).trans
            (hp.works.trans (frame_word hp.right.reduction doneB 248 (by decide)).symm)⟩
      obtain ⟨outputTrace, _⟩ := FinalOutput.code_rel v name p _ _ _ _ _ _ finalRelated outputA outputB
      exact ⟨by rw [reduceTrace, outputTrace], trivial⟩

end VG.Proof.Argon2.AArch64.Finish
end

/-! Merged from `Proof.Argon2.AArch64.FillSlicesCT`. -/
section
/-! Merged from `Proof.Argon2.AArch64.FillSlicesBodyCT`. -/
section
/-! Merged from `Proof.Argon2.AArch64.FillSliceCT`. -/
section
/-! Merged from `Proof.Argon2.AArch64.FillLanesCT`. -/
section
/-! Merged from `Proof.Argon2.AArch64.FillLanesBodyCT`. -/
section
/-! Lane iteration preserves public allocations and loops on the public lane count. -/

namespace VG.Proof.Argon2.AArch64.FillLanes

open VG VG.AArch64 VG.Spec.Argon2 VG.Impl.Argon2.AArch64.FillLanes

theorem advance_rel : RelCT isa (fun s t => s.gpr .x19 = t.gpr .x19 ∧ s.sp = t.sp)
    (.block advance) (fun _ _ => True) :=
  (RelCT.taintRegs (τ := Taint.ofRegs [.x19])
    (fun _ _ h => ⟨h.2, by
      intro r hr; simp only [Taint.mem_ofRegs, List.mem_singleton] at hr; subst r; exact h.1⟩)
    [] (by taint_decide)).mono (fun _ _ h => h) (fun _ _ _ => trivial)

structure NextRelated (p : Params) (pass lane slice : Nat) (leftState rightState : FillState) (s t : State) : Prop where
  ready : SegmentSetup.RelatedReady p pass lane slice s t
  leftMatrix : Proof.Argon2.Represents s.mem (FillKernel.matrix s) p.blocks leftState.memory
  rightMatrix : Proof.Argon2.Represents t.mem (FillKernel.matrix t) p.blocks rightState.memory

theorem body_rel (p : Params) (pass lane slice : Nat) (leftState rightState : FillState) :
    RelCT isa (SegmentSetup.Related p pass lane slice leftState rightState) body
      (fun s t => eval (.nonzero .x .x14) s = eval (.nonzero .x .x14) t ∧ (lane + 1 < p.lanes → NextRelated p pass (lane + 1) slice
        (Proof.Argon2.segment p pass lane slice 0 p.segmentLen leftState)
        (Proof.Argon2.segment p pass lane slice 0 p.segmentLen rightState) s t)) := by
  intro s t ts tt a b hp ea eb
  cases ea with
  | seq segmentA advanceA =>
    cases eb with
    | seq segmentB advanceB =>
      obtain ⟨segmentTrace, _⟩ := SegmentSetup.code_rel p pass lane slice leftState rightState
        _ _ _ _ _ _ hp segmentA segmentB
      obtain ⟨_, sa, runA, filledA⟩ := SegmentSetup.code_ok s p pass lane slice hp.ready.left leftState hp.leftMatrix
      obtain ⟨_, sb, runB, filledB⟩ := SegmentSetup.code_ok t p pass lane slice hp.ready.right rightState hp.rightMatrix
      obtain ⟨_, rfl⟩ := Exec.det segmentA runA
      obtain ⟨_, rfl⟩ := Exec.det segmentB runB
      have bases := (filledA.regs .x19 (by simp [FillCompress.loopRegs]) (by decide)).trans
        (hp.ready.bases.trans (filledB.regs .x19 (by simp [FillCompress.loopRegs]) (by decide)).symm)
      have stacks := filledA.sp.trans (hp.ready.stacks.trans filledB.sp.symm)
      obtain ⟨advancedTrace, _⟩ := advance_rel _ _ _ _ _ _ ⟨bases, stacks⟩ advanceA advanceB
      obtain ⟨_, a', runA, doneA⟩ := body_ok s p pass lane slice hp.ready.left leftState hp.leftMatrix
      obtain ⟨_, b', runB, doneB⟩ := body_ok t p pass lane slice hp.ready.right rightState hp.rightMatrix
      obtain ⟨_, rfl⟩ := Exec.det (.seq segmentA advanceA) runA
      obtain ⟨_, rfl⟩ := Exec.det (.seq segmentB advanceB) runB
      refine ⟨by rw [segmentTrace, advancedTrace], doneA.cf.trans doneB.cf.symm, ?_⟩
      intro active
      refine ⟨⟨doneA.next active, doneB.next active, ?_, ?_,
        doneA.matrix.trans (hp.ready.matrices.trans doneB.matrix.symm),
        doneA.work.trans (hp.ready.work.trans doneB.work.symm)⟩, doneA.represented, doneB.represented⟩
      · exact (doneA.regs .x19 (by simp [FillCompress.loopRegs]) (by decide) (by decide)).trans
          (hp.ready.bases.trans (doneB.regs .x19 (by simp [FillCompress.loopRegs]) (by decide) (by decide)).symm)
      · exact (doneA.sp).trans
          (hp.ready.stacks.trans (doneB.sp).symm)

end VG.Proof.Argon2.AArch64.FillLanes
end

/-! The lane loop exposes only the slice's specified reference log. -/

namespace VG.Proof.Argon2.AArch64.FillLanes

open VG VG.AArch64 VG.Spec.Argon2

structure Related (p : Params) (pass lane slice count : Nat) (leftState rightState : FillState)
    (s t : State) : Prop where
  ready : SegmentSetup.RelatedReady p pass lane slice s t
  leftMatrix : Proof.Argon2.Represents s.mem (FillKernel.matrix s) p.blocks leftState.memory
  rightMatrix : Proof.Argon2.Represents t.mem (FillKernel.matrix t) p.blocks rightState.memory
  indices : (Proof.Argon2.lanes p pass slice lane count leftState).indices =
    (Proof.Argon2.lanes p pass slice lane count rightState).indices

theorem loop_rel (p : Params) (pass lane slice count : Nat) (leftState rightState : FillState)
    (positive : 0 < count) (endLane : lane + count = p.lanes) :
    RelCT isa (Related p pass lane slice count leftState rightState) Impl.Argon2.AArch64.FillLanes.loop (fun _ _ => True) := by
  let I := fun n s t => ∃ (lane : Nat) (leftState rightState : FillState),
    lane + n = p.lanes ∧ 0 < n ∧ Related p pass lane slice n leftState rightState s t
  have steps : ∀ n, RelCT isa (I n) Impl.Argon2.AArch64.FillLanes.body fun s t =>
      isa.eval (.nonzero .x .x14) s = isa.eval (.nonzero .x .x14) t ∧ (isa.eval (.nonzero .x .x14) s = some false → True) ∧
        (isa.eval (.nonzero .x .x14) s = some true → ∃ m < n, I m s t) := by
    intro n s t ts tt a b hp ea eb
    obtain ⟨j, ls, rs, endLane, positive, hp⟩ := hp
    cases n with
    | zero => omega
    | succ n =>
      have segmentRelated : SegmentSetup.Related p pass j slice ls rs s t :=
        ⟨hp.ready, hp.leftMatrix, hp.rightMatrix, Proof.Argon2.lanes_first_segment p pass slice j n ls rs
          hp.ready.left.parameters.segment_bound.1 hp.indices⟩
      obtain ⟨trace, flags, next⟩ := body_rel p pass j slice ls rs _ _ _ _ _ _ segmentRelated ea eb
      obtain ⟨_, a', runA, done⟩ := body_ok s p pass j slice hp.ready.left ls hp.leftMatrix
      obtain ⟨_, rfl⟩ := Exec.det ea runA
      refine ⟨trace, ?_, fun _ => trivial, ?_⟩
      · exact flags
      · intro taken
        have active : j + 1 < p.lanes := by
          simp only [done.cf, Option.some.injEq, decide_eq_true_eq] at taken
          exact taken
        obtain ⟨ready, matrixA, matrixB⟩ := next active
        have indices := hp.indices
        rw [Proof.Argon2.lanes_succ, Proof.Argon2.lanes_succ] at indices
        exact ⟨n, by omega, j + 1, Proof.Argon2.segment p pass j slice 0 p.segmentLen ls,
          Proof.Argon2.segment p pass j slice 0 p.segmentLen rs, by omega, by omega, ready, matrixA, matrixB, indices⟩
  exact (RelCT.loop I steps count).mono
    (fun _ _ h => ⟨lane, leftState, rightState, endLane, positive, h⟩) (fun _ _ h => h)

end VG.Proof.Argon2.AArch64.FillLanes
end

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
end

/-! A slice iteration preserves public allocations and its public continuation guard. -/

namespace VG.Proof.Argon2.AArch64.FillSlices

open VG VG.AArch64 VG.Spec.Argon2 VG.Impl.Argon2.AArch64.FillSlices

theorem advance_rel : RelCT isa (fun s t : State => s.sp = t.sp)
    (.block advance) (fun _ _ => True) :=
  (RelCT.taintRegs (τ := Taint.ofRegs [])
    (fun _ _ h => ⟨h, by intro r hr; simp only [Taint.mem_ofRegs, List.not_mem_nil] at hr⟩)
    [] (by taint_decide)).mono (fun _ _ h => h) (fun _ _ _ => trivial)

structure NextRelated (p : Params) (pass slice : Nat) (leftState rightState : FillState) (s t : State) : Prop where
  left : FillSlice.Ready p pass slice s
  right : FillSlice.Ready p pass slice t
  bases : s.gpr .x19 = t.gpr .x19
  stacks : s.sp = t.sp
  matrices : FillKernel.matrix s = FillKernel.matrix t
  work : AddressCalls.work s = AddressCalls.work t
  leftMatrix : Proof.Argon2.Represents s.mem (FillKernel.matrix s) p.blocks leftState.memory
  rightMatrix : Proof.Argon2.Represents t.mem (FillKernel.matrix t) p.blocks rightState.memory

theorem body_rel (p : Params) (pass slice : Nat) (leftState rightState : FillState) :
    RelCT isa (FillSlice.Related p pass slice leftState rightState) body
      (fun s t => eval (.nonzero .x .x14) s = eval (.nonzero .x .x14) t ∧ (slice + 1 < 4 → NextRelated p pass (slice + 1)
        (Proof.Argon2.lanes p pass slice 0 p.lanes leftState) (Proof.Argon2.lanes p pass slice 0 p.lanes rightState) s t)) := by
  intro s t ts tt a b hp ea eb
  cases ea with
  | seq sliceA advanceA =>
    cases eb with
    | seq sliceB advanceB =>
      obtain ⟨sliceTrace, _⟩ := FillSlice.code_rel p pass slice leftState rightState _ _ _ _ _ _ hp sliceA sliceB
      obtain ⟨_, sa, fillRunA, filledA⟩ := FillSlice.code_ok s p pass slice hp.left leftState hp.leftMatrix
      obtain ⟨_, sb, fillRunB, filledB⟩ := FillSlice.code_ok t p pass slice hp.right rightState hp.rightMatrix
      obtain ⟨_, rfl⟩ := Exec.det sliceA fillRunA
      obtain ⟨_, rfl⟩ := Exec.det sliceB fillRunB
      have stacks := filledA.sp.trans (hp.stacks.trans filledB.sp.symm)
      obtain ⟨advanceTrace, _⟩ := advance_rel _ _ _ _ _ _ stacks advanceA advanceB
      obtain ⟨_, a', runA, doneA⟩ := body_ok s p pass slice hp.left leftState hp.leftMatrix
      obtain ⟨_, b', runB, doneB⟩ := body_ok t p pass slice hp.right rightState hp.rightMatrix
      obtain ⟨_, rfl⟩ := Exec.det (.seq sliceA advanceA) runA
      obtain ⟨_, rfl⟩ := Exec.det (.seq sliceB advanceB) runB
      refine ⟨by rw [sliceTrace, advanceTrace], doneA.cf.trans doneB.cf.symm, ?_⟩
      intro active
      refine ⟨doneA.next active, doneB.next active, ?_, ?_,
        doneA.matrix.trans (hp.matrices.trans doneB.matrix.symm),
        doneA.work.trans (hp.work.trans doneB.work.symm), doneA.represented, doneB.represented⟩
      · exact (doneA.regs .x19 (by simp [FillCompress.loopRegs]) (by decide) (by decide) (by decide)).trans
          (hp.bases.trans (doneB.regs .x19 (by simp [FillCompress.loopRegs]) (by decide) (by decide) (by decide)).symm)
      · exact (doneA.sp).trans
          (hp.stacks.trans (doneB.sp).symm)

end VG.Proof.Argon2.AArch64.FillSlices
end

/-! The complete pass leaks only its reviewed reference log, including Argon2id's mode change. -/

namespace VG.Proof.Argon2.AArch64.FillSlices

open VG VG.AArch64 VG.Spec.Argon2

structure Related (p : Params) (pass slice count : Nat) (leftState rightState : FillState) (s t : State) : Prop where
  states : NextRelated p pass slice leftState rightState s t
  indices : (Proof.Argon2.slices p pass slice count leftState).indices =
    (Proof.Argon2.slices p pass slice count rightState).indices

theorem loop_rel (p : Params) (pass slice count : Nat) (leftState rightState : FillState)
    (positive : 0 < count) (endSlice : slice + count = 4) :
    RelCT isa (Related p pass slice count leftState rightState) Impl.Argon2.AArch64.FillSlices.loop (fun _ _ => True) := by
  let I := fun n s t => ∃ (slice : Nat) (leftState rightState : FillState),
    slice + n = 4 ∧ 0 < n ∧ Related p pass slice n leftState rightState s t
  have steps : ∀ n, RelCT isa (I n) Impl.Argon2.AArch64.FillSlices.body fun s t =>
      isa.eval (.nonzero .x .x14) s = isa.eval (.nonzero .x .x14) t ∧ (isa.eval (.nonzero .x .x14) s = some false → True) ∧
        (isa.eval (.nonzero .x .x14) s = some true → ∃ m < n, I m s t) := by
    intro n s t ts tt a b hp ea eb
    obtain ⟨j, ls, rs, endSlice, positive, hp⟩ := hp
    cases n with
    | zero => omega
    | succ n =>
      have sliceRelated : FillSlice.Related p pass j ls rs s t :=
        ⟨hp.states.left, hp.states.right, hp.states.bases, hp.states.stacks, hp.states.matrices, hp.states.work,
          hp.states.leftMatrix, hp.states.rightMatrix, Proof.Argon2.slices_first_lane_fold p pass j n ls rs
            hp.states.left.parameters.segment_bound.1 hp.indices⟩
      obtain ⟨trace, flags, next⟩ := body_rel p pass j ls rs _ _ _ _ _ _ sliceRelated ea eb
      obtain ⟨_, a', runA, done⟩ := body_ok s p pass j hp.states.left ls hp.states.leftMatrix
      obtain ⟨_, rfl⟩ := Exec.det ea runA
      refine ⟨trace, ?_, fun _ => trivial, ?_⟩
      · exact flags
      · intro taken
        have active : j + 1 < 4 := by
          simp only [done.cf, Option.some.injEq, decide_eq_true_eq] at taken
          exact taken
        have indices := hp.indices
        rw [Proof.Argon2.slices_succ, Proof.Argon2.slices_succ] at indices
        exact ⟨n, by omega, j + 1, Proof.Argon2.lanes p pass j 0 p.lanes ls,
          Proof.Argon2.lanes p pass j 0 p.lanes rs, by omega, by omega, next active, indices⟩
  exact (RelCT.loop I steps count).mono
    (fun _ _ h => ⟨slice, leftState, rightState, endSlice, positive, h⟩) (fun _ _ h => h)

theorem pass_rel (p : Params) (pass : Nat) (leftState rightState : FillState) :
    RelCT isa (fun s t => NextRelated p pass 0 leftState rightState s t ∧
      (fillPass p leftState pass).indices = (fillPass p rightState pass).indices)
      Impl.Argon2.AArch64.FillSlices.loop (fun _ _ => True) := by
  refine (loop_rel p pass 0 4 leftState rightState (by decide) (by decide)).mono ?_ (fun _ _ h => h)
  intro s t h
  refine ⟨h.1, ?_⟩
  rw [Proof.Argon2.slices_pass p pass leftState, Proof.Argon2.slices_pass p pass rightState]
  exact h.2

end VG.Proof.Argon2.AArch64.FillSlices
end

/-! Merged from `Proof.Argon2.AArch64.FillIterationsCT`. -/
section
/-! Merged from `Proof.Argon2.AArch64.FillIterationsBodyCT`. -/
section
/-! Merged from `Proof.Argon2.AArch64.FillIterationCT`. -/
section
/-! Pass setup retains public pointers and exposes only the reviewed pass log. -/

namespace VG.Proof.Argon2.AArch64.FillIteration

open VG VG.AArch64 VG.Spec.Argon2

structure Related (p : Params) (pass : Nat) (leftState rightState : FillState) (s t : State) : Prop where
  left : Ready p pass s
  right : Ready p pass t
  bases : s.gpr .x19 = t.gpr .x19
  stacks : s.sp = t.sp
  matrices : FillKernel.matrix s = FillKernel.matrix t
  work : AddressCalls.work s = AddressCalls.work t
  leftMatrix : Proof.Argon2.Represents s.mem (FillKernel.matrix s) p.blocks leftState.memory
  rightMatrix : Proof.Argon2.Represents t.mem (FillKernel.matrix t) p.blocks rightState.memory
  indices : (fillPass p leftState pass).indices = (fillPass p rightState pass).indices

theorem setup_trace : RelCT isa (fun s t : State => s.sp = t.sp) (.block Impl.Argon2.AArch64.FillIteration.setup) (fun _ _ => True) :=
  (RelCT.taintRegs (τ := Taint.ofRegs [])
    (fun _ _ h => ⟨h, by intro r hr; simp only [Taint.mem_ofRegs, List.not_mem_nil] at hr⟩)
    [] (by taint_decide)).mono (fun _ _ h => h) (fun _ _ _ => trivial)

theorem setup_public_rel (p : Params) (pass : Nat) (leftState rightState : FillState) :
    RelCT isa (Related p pass leftState rightState) (.block Impl.Argon2.AArch64.FillIteration.setup)
      (fun s t => FillSlices.NextRelated p pass 0 leftState rightState s t ∧
        (fillPass p leftState pass).indices = (fillPass p rightState pass).indices) := by
  have trace := setup_trace.mono (P' := Related p pass leftState rightState)
    (fun _ _ h => h.stacks) (fun _ _ h => h)
  have full := trace.wpDep (fun s t h => ⟨setup_ok s p pass h.left, setup_ok t p pass h.right⟩)
  refine full.mono (fun _ _ h => h) ?_
  intro a b h
  obtain ⟨_, s, t, hp, ha, hb⟩ := h
  refine ⟨⟨ha.ready, hb.ready, ?_, ?_, ?_, ?_, ?_, ?_⟩, hp.indices⟩
  · rw [ha.keeps.regs .x19 (by decide), hb.keeps.regs .x19 (by decide)]; exact hp.bases
  · rw [ha.keeps.sp, hb.keeps.sp]; exact hp.stacks
  · unfold FillKernel.matrix
    rw [ha.keeps.mem, hb.keeps.mem, ha.keeps.regs .x19 (by decide), hb.keeps.regs .x19 (by decide)]; exact hp.matrices
  · unfold AddressCalls.work
    rw [ha.keeps.mem, hb.keeps.mem, ha.keeps.regs .x19 (by decide), hb.keeps.regs .x19 (by decide)]; exact hp.work
  · unfold FillKernel.matrix; rw [ha.keeps.mem, ha.keeps.regs .x19 (by decide)]; exact hp.leftMatrix
  · unfold FillKernel.matrix; rw [hb.keeps.mem, hb.keeps.regs .x19 (by decide)]; exact hp.rightMatrix

theorem code_rel (p : Params) (pass : Nat) (leftState rightState : FillState) :
    RelCT isa (Related p pass leftState rightState) Impl.Argon2.AArch64.FillIteration.code (fun _ _ => True) :=
  (setup_public_rel p pass leftState rightState).seq (FillSlices.pass_rel p pass leftState rightState)

end VG.Proof.Argon2.AArch64.FillIteration
end

/-! Iteration advances its public pass counter and retains the reviewed filling log. -/

namespace VG.Proof.Argon2.AArch64.FillIterations

open VG VG.AArch64 VG.Spec.Argon2 VG.Impl.Argon2.AArch64.FillIterations

theorem advance_rel : RelCT isa (fun s t => s.gpr .x19 = t.gpr .x19 ∧ s.sp = t.sp)
    advance (fun _ _ => True) :=
  (RelCT.taintRegs (τ := Taint.ofRegs [.x19])
    (fun _ _ h => ⟨h.2, by
      intro r hr; simp only [Taint.mem_ofRegs, List.mem_singleton] at hr; subst r; exact h.1⟩)
    [] (by taint_decide)).mono (fun _ _ h => h) (fun _ _ _ => trivial)

structure NextRelated (p : Params) (pass : Nat) (leftState rightState : FillState) (s t : State) : Prop where
  left : Ready p pass s
  right : Ready p pass t
  bases : s.gpr .x19 = t.gpr .x19
  stacks : s.sp = t.sp
  matrices : FillKernel.matrix s = FillKernel.matrix t
  work : AddressCalls.work s = AddressCalls.work t
  leftMatrix : Proof.Argon2.Represents s.mem (FillKernel.matrix s) p.blocks leftState.memory
  rightMatrix : Proof.Argon2.Represents t.mem (FillKernel.matrix t) p.blocks rightState.memory

theorem body_rel (p : Params) (pass : Nat) (leftState rightState : FillState) :
    RelCT isa (fun s t => NextRelated p pass leftState rightState s t ∧
      (fillPass p leftState pass).indices = (fillPass p rightState pass).indices) body
      (fun s t => eval (.nonzero .x .x14) s = eval (.nonzero .x .x14) t ∧ (pass + 1 < p.passes → NextRelated p (pass + 1)
        (fillPass p leftState pass)
        (fillPass p rightState pass) s t)) := by
  intro s t ts tt a b hp ea eb
  obtain ⟨hp, indices⟩ := hp
  have related : FillIteration.Related p pass leftState rightState s t :=
    ⟨hp.left.filling, hp.right.filling, hp.bases, hp.stacks, hp.matrices, hp.work, hp.leftMatrix, hp.rightMatrix, indices⟩
  cases ea with
  | seq segmentA advanceA =>
    cases eb with
    | seq segmentB advanceB =>
      obtain ⟨segmentTrace, _⟩ := FillIteration.code_rel p pass leftState rightState
        _ _ _ _ _ _ related segmentA segmentB
      obtain ⟨_, sa, runA, filledA⟩ := FillIteration.code_ok s p pass hp.left.filling leftState hp.leftMatrix
      obtain ⟨_, sb, runB, filledB⟩ := FillIteration.code_ok t p pass hp.right.filling rightState hp.rightMatrix
      obtain ⟨_, rfl⟩ := Exec.det segmentA runA
      obtain ⟨_, rfl⟩ := Exec.det segmentB runB
      have bases := (filledA.regs .x19 (by simp [FillCompress.loopRegs]) (by decide) (by decide) (by decide)).trans
        (hp.bases.trans (filledB.regs .x19 (by simp [FillCompress.loopRegs]) (by decide) (by decide) (by decide)).symm)
      have stacks := filledA.sp.trans (hp.stacks.trans filledB.sp.symm)
      obtain ⟨advancedTrace, _⟩ := advance_rel _ _ _ _ _ _ ⟨bases, stacks⟩ advanceA advanceB
      obtain ⟨_, a', runA, doneA⟩ := body_ok s p pass hp.left leftState hp.leftMatrix
      obtain ⟨_, b', runB, doneB⟩ := body_ok t p pass hp.right rightState hp.rightMatrix
      obtain ⟨_, rfl⟩ := Exec.det (.seq segmentA advanceA) runA
      obtain ⟨_, rfl⟩ := Exec.det (.seq segmentB advanceB) runB
      refine ⟨by rw [segmentTrace, advancedTrace], doneA.cf.trans doneB.cf.symm, ?_⟩
      intro active
      refine ⟨doneA.next active, doneB.next active, ?_, ?_,
        doneA.matrix.trans (hp.matrices.trans doneB.matrix.symm),
        doneA.work.trans (hp.work.trans doneB.work.symm), doneA.represented, doneB.represented⟩
      · exact (doneA.regs .x19 (by simp [FillCompress.loopRegs]) (by decide) (by decide) (by decide)).trans
          (hp.bases.trans (doneB.regs .x19 (by simp [FillCompress.loopRegs]) (by decide) (by decide) (by decide)).symm)
      · exact (doneA.sp).trans
          (hp.stacks.trans (doneB.sp).symm)

end VG.Proof.Argon2.AArch64.FillIterations
end

/-! The pass loop exposes only the complete filling reference log. -/

namespace VG.Proof.Argon2.AArch64.FillIterations

open VG VG.AArch64 VG.Spec.Argon2

structure Related (p : Params) (pass count : Nat) (leftState rightState : FillState)
    (s t : State) : Prop where
  ready : NextRelated p pass leftState rightState s t
  leftMatrix : Proof.Argon2.Represents s.mem (FillKernel.matrix s) p.blocks leftState.memory
  rightMatrix : Proof.Argon2.Represents t.mem (FillKernel.matrix t) p.blocks rightState.memory
  indices : (Proof.Argon2.iterations p pass count leftState).indices =
    (Proof.Argon2.iterations p pass count rightState).indices

theorem loop_rel (p : Params) (pass count : Nat) (leftState rightState : FillState)
    (positive : 0 < count) (endPass : pass + count = p.passes) :
    RelCT isa (Related p pass count leftState rightState) Impl.Argon2.AArch64.FillIterations.loop (fun _ _ => True) := by
  let I := fun n s t => ∃ (pass : Nat) (leftState rightState : FillState),
    pass + n = p.passes ∧ 0 < n ∧ Related p pass n leftState rightState s t
  have steps : ∀ n, RelCT isa (I n) Impl.Argon2.AArch64.FillIterations.body fun s t =>
      isa.eval (.nonzero .x .x14) s = isa.eval (.nonzero .x .x14) t ∧ (isa.eval (.nonzero .x .x14) s = some false → True) ∧
        (isa.eval (.nonzero .x .x14) s = some true → ∃ m < n, I m s t) := by
    intro n s t ts tt a b hp ea eb
    obtain ⟨j, ls, rs, endPass, positive, hp⟩ := hp
    cases n with
    | zero => omega
    | succ n =>
      have passIndices := Proof.Argon2.iterations_first_pass p j n ls rs
        hp.ready.left.filling.parameters.segment_bound.1 hp.indices
      obtain ⟨trace, flags, next⟩ := body_rel p j ls rs _ _ _ _ _ _ ⟨hp.ready, passIndices⟩ ea eb
      obtain ⟨_, a', runA, done⟩ := body_ok s p j hp.ready.left ls hp.leftMatrix
      obtain ⟨_, rfl⟩ := Exec.det ea runA
      refine ⟨trace, ?_, fun _ => trivial, ?_⟩
      · exact flags
      · intro taken
        have active : j + 1 < p.passes := by
          simp only [done.cf, Option.some.injEq, decide_eq_true_eq] at taken
          exact taken
        have ready := next active
        have indices := hp.indices
        rw [Proof.Argon2.iterations_succ, Proof.Argon2.iterations_succ] at indices
        exact ⟨n, by omega, j + 1, fillPass p ls j,
          fillPass p rs j, by omega, by omega, ready, ready.leftMatrix, ready.rightMatrix, indices⟩
  exact (RelCT.loop I steps count).mono
    (fun _ _ h => ⟨pass, leftState, rightState, endPass, positive, h⟩) (fun _ _ h => h)

end VG.Proof.Argon2.AArch64.FillIterations
end

/-! Merged from `Proof.Argon2.AArch64.FillFinishCT`. -/
section
/-! Filling and finalization expose only the reviewed filling reference log. -/

namespace VG.Proof.Argon2.AArch64.FillFinish

open VG VG.AArch64 VG.Spec.Argon2 ReductionState

structure Related (p : Params) (leftState rightState : FillState) (s t : State) : Prop where
  left : Ready p s
  right : Ready p t
  bases : s.gpr .x19 = t.gpr .x19
  stacks : s.sp = t.sp
  matrices : matrix s = matrix t
  outputs : FinalOutput.output s = FinalOutput.output t
  works : FinalOutput.work s = FinalOutput.work t
  leftMatrix : Proof.Argon2.Represents s.mem (matrix s) p.blocks leftState.memory
  rightMatrix : Proof.Argon2.Represents t.mem (matrix t) p.blocks rightState.memory
  indices : (Proof.Argon2.iterations p 0 p.passes leftState).indices =
    (Proof.Argon2.iterations p 0 p.passes rightState).indices

theorem code_rel (v : HPrime.Backend) (name : String) (p : Params)
    (leftState rightState : FillState) :
    RelCT isa (Related p leftState rightState) (Impl.Argon2.AArch64.FillFinish.code name v.hash)
      (fun _ _ => True) := by
  intro s t ts tt a b hp ea eb
  cases ea with
  | seq fillA finishA =>
    cases eb with
    | seq fillB finishB =>
      have related : FillIterations.Related p 0 p.passes leftState rightState s t :=
        ⟨⟨hp.left.filling, hp.right.filling, hp.bases, hp.stacks, hp.matrices, hp.works, hp.leftMatrix, hp.rightMatrix⟩,
          hp.leftMatrix, hp.rightMatrix, hp.indices⟩
      obtain ⟨fillTrace, _⟩ := FillIterations.loop_rel p 0 p.passes leftState rightState hp.left.positive
        (Nat.zero_add _) _ _ _ _ _ _ related fillA fillB
      obtain ⟨_, sa, runA, doneA⟩ := FillIterations.loop_ok p.passes s p 0 hp.left.filling leftState
        hp.leftMatrix hp.left.positive (Nat.zero_add _)
      obtain ⟨_, sb, runB, doneB⟩ := FillIterations.loop_ok p.passes t p 0 hp.right.filling rightState
        hp.rightMatrix hp.right.positive (Nat.zero_add _)
      obtain ⟨_, rfl⟩ := Exec.det fillA runA
      obtain ⟨_, rfl⟩ := Exec.det fillB runB
      have finalRelated : Finish.Related p (Proof.Argon2.iterations p 0 p.passes leftState).memory
          (Proof.Argon2.iterations p 0 p.passes rightState).memory _ _ :=
        ⟨finish_ready hp.left.filling hp.left.finish doneA, finish_ready hp.right.filling hp.right.finish doneB,
          (doneA.regs .x19 (by simp [FillCompress.loopRegs]) (by decide) (by decide) (by decide)).trans
            (hp.bases.trans (doneB.regs .x19 (by simp [FillCompress.loopRegs]) (by decide) (by decide) (by decide)).symm),
          (doneA.sp).trans
            (hp.stacks.trans (doneB.sp).symm),
          doneA.matrix.trans (hp.matrices.trans doneB.matrix.symm),
          (doneA.frame_word hp.left.filling 256 (by decide) (by decide)).trans
            (hp.outputs.trans (doneB.frame_word hp.right.filling 256 (by decide) (by decide)).symm),
          (doneA.frame_word hp.left.filling 248 (by decide) (by decide)).trans
            (hp.works.trans (doneB.frame_word hp.right.filling 248 (by decide) (by decide)).symm),
          doneA.represented, doneB.represented⟩
      obtain ⟨finishTrace, _⟩ := Finish.code_rel v name p _ _ _ _ _ _ _ _ finalRelated finishA finishB
      exact ⟨by rw [fillTrace, finishTrace], trivial⟩

end VG.Proof.Argon2.AArch64.FillFinish
end

/-! The entire post-H₀ pipeline leaks only the reviewed complete filling reference log. -/

namespace VG.Proof.Argon2.AArch64.InitFill

open VG VG.AArch64 VG.Spec.Argon2
open VG.Spec.Blake2 (bytesAt)

def initial (p : Params) (s : State) : FillState := initMemory p (bytesAt s.mem (s.gpr .x19) 64)

structure Related (p : Params) (s t : State) : Prop where
  left : Ready p s
  right : Ready p t
  bases : s.gpr .x19 = t.gpr .x19
  stacks : s.sp = t.sp
  matrices : FillKernel.matrix s = FillKernel.matrix t
  outputs : FinalOutput.output s = FinalOutput.output t
  works : FinalOutput.work s = FinalOutput.work t
  indices : (Proof.Argon2.iterations p 0 p.passes (initial p s)).indices =
    (Proof.Argon2.iterations p 0 p.passes (initial p t)).indices

theorem code_rel (v : HPrime.Backend) (name : String) (p : Params) :
    RelCT isa (Related p) (Impl.Argon2.AArch64.InitFill.code name v.hash) (fun _ _ => True) := by
  intro s t ts tt a b hp ea eb
  have params := hp.left.environment.parameters
  have q : 2 ≤ p.laneLen := by
    have segments := Proof.Argon2.laneLen_segments p params.lanesPositive
    have minimum := params.segment_bound.1
    omega
  have lanesBound : p.lanes < 2 ^ 64 := Nat.lt_trans params.lanesBound (by decide)
  have pub : MemoryInit.AgreeBases s t := by
    refine ⟨hp.stacks, ?_⟩
    intro r hr
    simp only [MemoryInit.publicBases, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hp.bases
    · exact hp.left.scratch.trans (hp.works.trans hp.right.scratch.symm)
    · exact hp.left.initializing.laneLength.trans hp.right.initializing.laneLength.symm
  have rightReady : MemoryInit.Ready (FillKernel.matrix s) p.lanes p.laneLen t := by
    rw [hp.matrices]; exact hp.right.initializing
  cases ea with
  | seq initA restA =>
    cases eb with
    | seq initB restB =>
      have initTrace := MemoryInit.code_ct v name (FillKernel.matrix s) p.lanes p.laneLen
        params.lanesPositive lanesBound q _ _ _ _ _ _ hp.left.initializing rightReady pub initA initB
      obtain ⟨_, sa, runA, doneA⟩ := MemoryInit.complete_ok v name s (FillKernel.matrix s) p.lanes p.laneLen
        hp.left.initializing params.lanesPositive lanesBound q
      obtain ⟨_, sb, runB, doneB⟩ := MemoryInit.complete_ok v name t (FillKernel.matrix t) p.lanes p.laneLen
        hp.right.initializing params.lanesPositive lanesBound q
      obtain ⟨_, rfl⟩ := Exec.det initA runA
      obtain ⟨_, rfl⟩ := Exec.det initB runB
      cases restA with
      | seq setupA fillA =>
        cases restB with
        | seq setupB fillB =>
          have bases := doneA.bp.trans (hp.bases.trans doneB.bp.symm)
          obtain ⟨setupTrace, _⟩ := FillSetup.code_rel _ _ _ _ _ _ ⟨bases, doneA.sp.trans (hp.stacks.trans doneB.sp.symm)⟩ setupA setupB
          obtain ⟨_, ca, runA, preparedA⟩ := FillSetup.code_ok _ p (initialized_setup hp.left doneA)
          obtain ⟨_, cb, runB, preparedB⟩ := FillSetup.code_ok _ p (initialized_setup hp.right doneB)
          obtain ⟨_, rfl⟩ := Exec.det setupA runA
          obtain ⟨_, rfl⟩ := Exec.det setupB runB
          have preparedBases := (preparedA.regs .x19 (by simp [FillCompress.loopRegs]) (by decide) (by decide) (by decide) (by decide)).trans
            (bases.trans (preparedB.regs .x19 (by simp [FillCompress.loopRegs]) (by decide) (by decide) (by decide) (by decide)).symm)
          have preparedStacks := preparedA.sp.trans
            ((doneA.sp.trans (hp.stacks.trans doneB.sp.symm)).trans
              preparedB.sp.symm)
          have initMatrices := (doneA.frame_word hp.left.initializing.space 232 (by decide) (Or.inr (by decide))).trans
            (hp.matrices.trans (doneB.frame_word hp.right.initializing.space 232 (by decide) (Or.inr (by decide))).symm)
          have matrices := preparedA.matrix.trans (initMatrices.trans preparedB.matrix.symm)
          have initOutputs := (doneA.frame_word hp.left.initializing.space 256 (by decide) (Or.inr (by decide))).trans
            (hp.outputs.trans (doneB.frame_word hp.right.initializing.space 256 (by decide) (Or.inr (by decide))).symm)
          have outputs := (preparedA.words 256 (by decide) (by decide)).trans
            (initOutputs.trans (preparedB.words 256 (by decide) (by decide)).symm)
          have initWorks := (doneA.frame_word hp.left.initializing.space 248 (by decide) (Or.inr (by decide))).trans
            (hp.works.trans (doneB.frame_word hp.right.initializing.space 248 (by decide) (Or.inr (by decide))).symm)
          have works := (preparedA.words 248 (by decide) (by decide)).trans
            (initWorks.trans (preparedB.words 248 (by decide) (by decide)).symm)
          have related : FillFinish.Related p (initial p s) (initial p t) _ _ :=
            ⟨preparedA.finish_ready (initialized_setup hp.left doneA) (initialized_output hp.left doneA) hp.left.positive,
              preparedB.finish_ready (initialized_setup hp.right doneB) (initialized_output hp.right doneB) hp.right.positive,
              preparedBases, preparedStacks, matrices, outputs, works,
              preparedA.represents (initialized_setup hp.left doneA) _ (initialized_represents hp.left doneA),
              preparedB.represents (initialized_setup hp.right doneB) _ (initialized_represents hp.right doneB), hp.indices⟩
          obtain ⟨fillTrace, _⟩ := FillFinish.code_rel v name p (initial p s) (initial p t) _ _ _ _ _ _ related fillA fillB
          exact ⟨by rw [initTrace, setupTrace, fillTrace], trivial⟩

end VG.Proof.Argon2.AArch64.InitFill
end

/-! Complete derivation reveals only its reviewed filling reference sequence. -/

namespace VG.Proof.Argon2.AArch64.InitialBody

open VG VG.AArch64 VG.Spec.Argon2
open VG.Impl.Argon2.AArch64.Initial
open VG.Spec.Blake2 (bytesAt)

def initial (p : Params) (s : State) : FillState := initMemory p (initialHash p
  (Initial.inputBytes s passwordOffset passwordLenOffset)
  (Initial.inputBytes s saltOffset saltLenOffset)
  (Initial.inputBytes s secretOffset secretLenOffset)
  (Initial.inputBytes s adOffset adLenOffset))

structure Related (p : Params) (s t : State) : Prop where
  left : Ready p s
  right : Ready p t
  hashing : Initial.Related s t
  matrices : FillKernel.matrix s = FillKernel.matrix t
  outputs : FinalOutput.output s = FinalOutput.output t
  works : FinalOutput.work s = FinalOutput.work t
  indices : (Proof.Argon2.iterations p 0 p.passes (initial p s)).indices =
    (Proof.Argon2.iterations p 0 p.passes (initial p t)).indices

theorem code_rel (v : HPrime.Backend) (name : String) (p : Params) :
    RelCT isa (Related p) (Impl.Argon2.AArch64.InitialBody.code name v.hash) (fun _ _ => True) := by
  have hashed := ((Initial.code_rel v).mono (P' := Related p) (fun _ _ h => h.hashing)
    (fun _ _ h => h)).wpDep (fun s t h =>
      ⟨Initial.initialHash_ok v s h.left.hashSpace h.left.inputs p h.left.header,
        Initial.initialHash_ok v t h.right.hashSpace h.right.inputs p h.right.header⟩)
  refine hashed.seq ((InitFill.code_rel v name p).mono ?_ (fun _ _ h => h))
  rintro a b ⟨_, s, t, hp, ⟨da, ha⟩, ⟨db, hb⟩⟩
  have baseA : FillKernel.matrix a = FillKernel.matrix s := ha.frame_word hp.left.hashSpace 232 (by decide) (by decide)
  have baseB : FillKernel.matrix b = FillKernel.matrix t := hb.frame_word hp.right.hashSpace 232 (by decide) (by decide)
  have outputA : FinalOutput.output a = FinalOutput.output s := ha.frame_word hp.left.hashSpace 256 (by decide) (by decide)
  have outputB : FinalOutput.output b = FinalOutput.output t := hb.frame_word hp.right.hashSpace 256 (by decide) (by decide)
  have workA : FinalOutput.work a = FinalOutput.work s := ha.frame_word hp.left.hashSpace 248 (by decide) (by decide)
  have workB : FinalOutput.work b = FinalOutput.work t := hb.frame_word hp.right.hashSpace 248 (by decide) (by decide)
  refine ⟨hashed_ready hp.left.filling hp.left.hashSpace ha, hashed_ready hp.right.filling hp.right.hashSpace hb,
    ha.x19.trans (hp.hashing.bp.trans hb.x19.symm), ha.sp.trans (hp.hashing.sp.trans hb.sp.symm),
    baseA.trans (hp.matrices.trans baseB.symm), outputA.trans (hp.outputs.trans outputB.symm),
    workA.trans (hp.works.trans workB.symm), ?_⟩
  unfold InitFill.initial
  rw [ha.x19, hb.x19, da, db]
  exact hp.indices

end VG.Proof.Argon2.AArch64.InitialBody
end

/-! Use exactly the flattened leakage allowance of the shared derive contract. -/

namespace VG.Proof.Argon2.AArch64.InitialBody

open VG VG.AArch64 VG.Spec.Argon2
open VG.Impl.Argon2.AArch64.Initial

def references (p : Params) (s : State) : List Nat := Spec.Argon2.references p
  (Initial.inputBytes s passwordOffset passwordLenOffset)
  (Initial.inputBytes s saltOffset saltLenOffset)
  (Initial.inputBytes s secretOffset secretLenOffset)
  (Initial.inputBytes s adOffset adLenOffset)

structure ReviewedRelated (p : Params) (s t : State) : Prop where
  left : Ready p s
  right : Ready p t
  hashing : Initial.Related s t
  matrices : FillKernel.matrix s = FillKernel.matrix t
  outputs : FinalOutput.output s = FinalOutput.output t
  works : FinalOutput.work s = FinalOutput.work t
  references : references p s = references p t

theorem ReviewedRelated.related {p : Params} {s t : State} (h : ReviewedRelated p s t) : Related p s t := by
  refine ⟨h.left, h.right, h.hashing, h.matrices, h.outputs, h.works, ?_⟩
  have parameters := h.left.filling.environment.parameters
  have positive : 0 < p.laneLen := by
    have segments := Proof.Argon2.laneLen_segments p parameters.lanesPositive
    have minimum := parameters.segment_bound.1
    omega
  have indices := Proof.Argon2.references_injective p positive _ _ _ _ _ _ _ _ h.references
  unfold initial
  rw [Proof.Argon2.iterations_fill, Proof.Argon2.iterations_fill]
  exact indices

theorem reviewed_rel (v : HPrime.Backend) (name : String) (p : Params) :
    RelCT isa (ReviewedRelated p) (Impl.Argon2.AArch64.InitialBody.code name v.hash) (fun _ _ => True) :=
  (code_rel v name p).mono (fun _ _ h => h.related) (fun _ _ h => h)

end VG.Proof.Argon2.AArch64.InitialBody
end

/-! Preserve precisely the reviewed leakage relation across parameter computation. -/

namespace VG.Proof.Argon2.AArch64.InitialBody

open VG VG.AArch64 VG.Spec.Argon2
open VG.Impl.Argon2.AArch64.Initial

theorem ReviewedRelated.of_state {s₁ s₂ t₁ t₂ : State} {p : Params}
    (h : ReviewedRelated p s₁ s₂) (k₁ : SameFrame s₁ t₁) (k₂ : SameFrame s₂ t₂)
    (length₁ : t₁.gpr .x21 = BitVec.ofNat 64 p.laneLen)
    (length₂ : t₂.gpr .x21 = BitVec.ofNat 64 p.laneLen) : ReviewedRelated p t₁ t₂ := by
  refine ⟨h.left.of_state k₁ length₁, h.right.of_state k₂ length₂, ?_, ?_, ?_, ?_, ?_⟩
  · refine ⟨⟨k₁.hashSpace h.hashing.left.space,
      fun input hi => k₁.input (h.hashing.left.inputs input hi)⟩,
      ⟨k₂.hashSpace h.hashing.right.space,
      fun input hi => k₂.input (h.hashing.right.inputs input hi)⟩, ?_, ?_, ?_, ?_⟩
    · rw [k₁.bp, k₂.bp]; exact h.hashing.bp
    · rw [k₁.bx, k₂.bx]; exact h.hashing.bx
    · rw [k₁.sp, k₂.sp]; exact h.hashing.sp
    · intro d hd; rw [k₁.word d, k₂.word d]; exact h.hashing.words d hd
  · unfold FillKernel.matrix; rw [k₁.mem, k₂.mem, k₁.bp, k₂.bp]; exact h.matrices
  · unfold FinalOutput.output; rw [k₁.mem, k₂.mem, k₁.bp, k₂.bp]; exact h.outputs
  · unfold FinalOutput.work; rw [k₁.mem, k₂.mem, k₁.bp, k₂.bp]; exact h.works
  · unfold VG.Proof.Argon2.AArch64.InitialBody.references
    rw [k₁.inputBytes passwordOffset passwordLenOffset, k₂.inputBytes passwordOffset passwordLenOffset,
      k₁.inputBytes saltOffset saltLenOffset, k₂.inputBytes saltOffset saltLenOffset,
      k₁.inputBytes secretOffset secretLenOffset, k₂.inputBytes secretOffset secretLenOffset,
      k₁.inputBytes adOffset adLenOffset, k₂.inputBytes adOffset adLenOffset]
    exact h.references

end VG.Proof.Argon2.AArch64.InitialBody
