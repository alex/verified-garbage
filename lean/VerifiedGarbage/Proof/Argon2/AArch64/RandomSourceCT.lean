import VerifiedGarbage.Proof.Argon2.AArch64.RandomSourcePrepare
import VerifiedGarbage.Proof.Argon2.AArch64.AddressModeCT
import VerifiedGarbage.Proof.Argon2.AArch64.AddressCacheSelectCT
import VerifiedGarbage.Proof.Argon2.AArch64.DependentWordCT

/-! Source dispatch and cached-word selection use only public addresses and guards. -/

namespace VG.Proof.Argon2.AArch64.RandomSource

open VG VG.AArch64 VG.Spec.Argon2 VG.Impl.Argon2.AArch64.RandomSource

structure Related (p : Params) (pass lane slice index old : Nat) (s t : State) : Prop where
  left : Ready p pass lane slice index old s
  right : Ready p pass lane slice index old t
  bases : s.gpr .x19 = t.gpr .x19
  stacks : s.sp = t.sp
  matrices : FillKernel.matrix s = FillKernel.matrix t
  work : AddressCalls.work s = AddressCalls.work t

theorem Related.of_keeps {p : Params} {pass lane slice index old : Nat} {s t a b : State}
    (h : Related p pass lane slice index old s t)
    (ka : Divide.Keeps ReferenceMap.changed s a) (kb : Divide.Keeps ReferenceMap.changed t b) :
    Related p pass lane slice index old a b := by
  refine ⟨h.left.of_keeps ka, h.right.of_keeps kb, ?_, ?_, ?_, ?_⟩
  · rw [ka.regs .x19 (by decide), kb.regs .x19 (by decide)]; exact h.bases
  · rw [ka.sp, kb.sp]; exact h.stacks
  · unfold FillKernel.matrix
    rw [ka.mem, kb.mem, ka.regs .x19 (by decide), kb.regs .x19 (by decide)]
    exact h.matrices
  · unfold AddressCalls.work
    rw [ka.mem, kb.mem, ka.regs .x19 (by decide), kb.regs .x19 (by decide)]
    exact h.work

theorem test_rel : RelCT isa (fun s t : State => s.sp = t.sp) (.block test)
    (fun s t => s.sp = t.sp) :=
  (RelCT.taintRegs (τ := Taint.ofRegs [])
    (fun _ _ h => ⟨h, by intro r hr; simp only [Taint.mem_ofRegs, List.not_mem_nil] at hr⟩)
    [] (by taint_decide)).mono (fun _ _ h => h) (fun _ _ h => h.1)

theorem prepare_rel (p : Params) (pass lane slice index old : Nat) :
    RelCT isa (Related p pass lane slice index old) prepare
      (fun s t => Related p pass lane slice index old s t ∧ eval (.zero .x .x15) s = eval (.zero .x .x15) t) := by
  have trace := AddressMode.code_rel.seq test_rel
  have narrowed := trace.mono (P' := Related p pass lane slice index old)
    (fun _ _ h => ⟨h.bases, h.stacks⟩) (fun _ _ h => h)
  have full := narrowed.wpDep (fun s t h =>
    ⟨prepare_ok s p pass lane slice index old h.left,
      prepare_ok t p pass lane slice index old h.right⟩)
  refine full.mono (fun _ _ h => h) ?_
  intro a b h
  obtain ⟨_, s, t, hp, ⟨fa, ka⟩, ⟨fb, kb⟩⟩ := h
  exact ⟨hp.of_keeps ka kb, fa.trans fb.symm⟩

theorem Related.cache {p : Params} {pass lane slice index old : Nat} {s t : State}
    (h : Related p pass lane slice index old s t) : AddressCache.ReadyRelated p pass lane slice old s t := by
  refine ⟨h.left.cache.ready, h.right.cache.ready,
    ⟨⟨⟨h.left.cache.layout, h.right.cache.layout, h.bases, h.stacks, h.work⟩,
      h.left.cache.reads, h.right.cache.reads⟩, ?_, ?_, h.left.cache.write, h.right.cache.write⟩⟩
  · exact h.left.filling.position.index.trans h.right.filling.position.index.symm
  · exact h.left.cache.words.counterWord.trans h.right.cache.words.counterWord.symm

theorem code_rel (p : Params) (pass lane slice index old : Nat) :
    RelCT isa (Related p pass lane slice index old) code (fun s t => s.sp = t.sp) := by
  have branches : RelCT isa
      (fun s t => Related p pass lane slice index old s t ∧ eval (.zero .x .x15) s = eval (.zero .x .x15) t)
      (.ite (.zero .x .x15) Impl.Argon2.AArch64.DependentWord.code Impl.Argon2.AArch64.AddressCache.code)
      (fun s t => s.sp = t.sp) := by
    apply RelCT.ite (by intro s t h; exact h.2)
    · exact (DependentWord.code_rel p pass lane slice index).mono
        (fun _ _ h => ⟨h.1.1.left.filling, h.1.1.right.filling, h.1.1.bases, h.1.1.stacks, h.1.1.matrices⟩)
        (fun _ _ h => h)
    · exact (AddressCache.code_rel p pass lane slice old).mono
        (fun _ _ h => h.1.1.cache) (fun _ _ h => h)
  exact (prepare_rel p pass lane slice index old).seq branches

end VG.Proof.Argon2.AArch64.RandomSource
