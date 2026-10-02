import VerifiedGarbage.Proof.Argon2.X86_64.InitialUpdateReady
import VerifiedGarbage.Proof.Framework.RelCTAssoc

/-! H₀ updates depend on public lengths and pointers, never on input contents. -/

namespace VG.Proof.Argon2.X86_64.Initial

open VG VG.X86_64 VG.Impl.Argon2.X86_64.Initial

def PrefixRelated (lo : Nat) (a b : State) : Prop :=
  True ∧ ∃ s t, RelatedRegs [.r12] s t ∧ LengthArgs s lo a ∧ LengthArgs t lo b

theorem prefix_rel (v : Proof.Blake2.X86_64.Backend) (lo : Nat) (slot : lo ∈ slots)
    (bound : lo + 8 ≤ 272)
    (check : ∃ hint, (taint.check (Taint.ofRegs [.rbp, .rbx]) (.block (lengthArgs lo)) hint).isSome = true) :
    RelCT isa (RelatedRegs [.r12])
      (.seq (.block (lengthArgs lo)) (Impl.Argon2.X86_64.HPrime.update (HPrime.hash v))) (LengthRelated lo) := by
  have args := ((lengthArgs_rel lo check).mono (P' := RelatedRegs [.r12])
    (fun _ _ h => ⟨h.1.bp, h.1.bx⟩) (fun _ _ h => h)).wpDep
    (fun s t h => ⟨lengthArgs_ok s lo (h.1.left.space.readable lo slot)
      (by simpa using h.1.left.space.write 792 4 (by decide)),
      lengthArgs_ok t lo (h.1.right.space.readable lo slot)
      (by simpa using h.1.right.space.write 792 4 (by decide))⟩)
  have call := HPrime.update_rel v (P := PrefixRelated lo) (fun a b ⟨_, s, t, hp, ha, hb⟩ =>
    ⟨prefix_update_ready hp.1.left.space ha, prefix_update_ready hp.1.right.space hb,
      by rw [ha.keeps.rbx, hb.keeps.rbx, hp.1.bx], by rw [ha.count, hb.count]; exact hp.2 _ (by simp),
      by rw [ha.pointer, hb.pointer, hp.1.bx], by rw [ha.size, hb.size],
      by rw [ha.keeps.rsp, hb.keeps.rsp, hp.1.sp]⟩)
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
        · rw [ha.other _ (by decide) (by decide) (by decide) (by decide),
            hb.other _ (by decide) (by decide) (by decide) (by decide)]
          exact hp.2 _ (by simp)
        · rw [ha.length, hb.length]; exact hp.1.words lo slot
      · rw [hp.1.left.space.word_keeps ha.keeps lo bound]; exact ha.length
      · rw [hp.1.right.space.word_keeps hb.keeps lo bound]; exact hb.length
    exact prepared.hash_keeps bound ka kb)
  exact args.seq finished

def InputRelated (lo po : Nat) (a b : State) : Prop :=
  True ∧ ∃ s t, LengthRelated lo s t ∧ InputArgs s a po ∧ InputArgs t b po

theorem input_rel (v : Proof.Blake2.X86_64.Backend) (po lo : Nat) (input : (po, lo) ∈ inputs)
    (check : ∃ hint, (taint.check (Taint.ofRegs [.rbp]) (.block (inputArgs po)) hint).isSome = true) :
    RelCT isa (LengthRelated lo)
      (.seq (.block (inputArgs po)) (Impl.Argon2.X86_64.HPrime.update (HPrime.hash v))) (LengthRelated lo) := by
  have args := ((inputArgs_rel po check).mono (P' := LengthRelated lo)
    (fun _ _ h => h.related.1.bp) (fun _ _ h => h)).wpDep
    (fun s t h => ⟨inputArgs_ok s po (h.related.1.left.space.readable po (h.related.1.left.inputs _ input).pointerSlot),
      inputArgs_ok t po (h.related.1.right.space.readable po (h.related.1.right.inputs _ input).pointerSlot)⟩)
  have call := HPrime.update_rel v (P := InputRelated lo po) (fun a b ⟨_, s, t, hp, ha, hb⟩ =>
    ⟨input_update_ready (hp.related.1.left.inputs _ input) hp.leftLength ha,
      input_update_ready (hp.related.1.right.inputs _ input) hp.rightLength hb,
      by rw [ha.keeps.rbx, hb.keeps.rbx, hp.related.1.bx],
      by rw [ha.count, hb.count, hp.related.2 .r12 (by simp)],
      by rw [ha.pointer, hb.pointer]; exact hp.related.1.words po (hp.related.1.left.inputs _ input).pointerSlot,
      by rw [ha.length, hb.length]; exact hp.related.2 .r14 (by simp),
      by rw [ha.keeps.rsp, hb.keeps.rsp, hp.related.1.sp]⟩)
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
        · rw [ha.total, hb.total, hp.related.2 .r12 (by simp)]
        · rw [ha.other _ (by decide) (by decide) (by decide) (by decide),
            hb.other _ (by decide) (by decide) (by decide) (by decide)]
          exact hp.related.2 .r14 (by simp)
      · rw [left.space.word_keeps ha.keeps lo left.lengthBound,
          ha.other _ (by decide) (by decide) (by decide) (by decide)]
        exact hp.leftLength
      · rw [right.space.word_keeps hb.keeps lo right.lengthBound,
          hb.other _ (by decide) (by decide) (by decide) (by decide)]
        exact hp.rightLength
    exact prepared.hash_keeps left.lengthBound ka kb)
  exact args.seq finished

theorem addCount_rel (lo : Nat) :
    RelCT isa (LengthRelated lo) (.block [.alu .add .r12 (.reg .r14)]) (RelatedRegs [.r12]) := by
  have ct := (RelCT.taint (A := taint) (P := LengthRelated lo) (Taint.ofRegs [])
    (fun _ _ _ => Taint.agree_ofRegs (by simp))
    (c := .block [.alu .add .r12 (.reg .r14)]) (by taint_decide)).wpDep
    (fun s t _ => ⟨addCount_ok s, addCount_ok t⟩)
  apply ct.mono (fun _ _ h => h)
  rintro a b ⟨_, s, t, hp, ⟨ca, _, ka⟩, ⟨cb, _, kb⟩⟩
  refine ⟨hp.related.1.keeps ka kb, ?_⟩
  intro r hr
  simp only [List.mem_singleton] at hr; subst r
  rw [ca, cb, hp.related.2 .r12 (by simp), hp.related.2 .r14 (by simp)]

theorem absorb_rel (v : Proof.Blake2.X86_64.Backend) (po lo : Nat) (input : (po, lo) ∈ inputs)
    (lengthCheck : ∃ hint, (taint.check (Taint.ofRegs [.rbp, .rbx]) (.block (lengthArgs lo)) hint).isSome = true)
    (pointerCheck : ∃ hint, (taint.check (Taint.ofRegs [.rbp]) (.block (inputArgs po)) hint).isSome = true) :
    RelCT isa (RelatedRegs [.r12]) (absorb (HPrime.hash v) po lo) (RelatedRegs [.r12]) := by
  have slot : lo ∈ slots := by
    have all : ∀ p ∈ inputs, p.2 ∈ slots := by decide
    exact all _ input
  have bound : lo + 8 ≤ 272 := by
    have all : ∀ d ∈ slots, d + 8 ≤ 272 := by decide
    exact all lo slot
  exact ((prefix_rel v lo slot bound lengthCheck).seq
    (((input_rel v po lo input pointerCheck).seq (addCount_rel lo)).assoc)).assoc

end VG.Proof.Argon2.X86_64.Initial
