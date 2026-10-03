import VerifiedGarbage.Proof.Argon2.X86_64.RandomSourcePrepare
import VerifiedGarbage.Proof.Argon2.X86_64.DependentWord
import VerifiedGarbage.Proof.Argon2.X86_64.FillKernelStable

/-! Merged from `Proof.Argon2.X86_64.DependentWordState`. -/
section
/-! The dependent source hands the filling step its random word and unchanged matrix. -/

namespace VG.Proof.Argon2.X86_64.DependentWord

open VG VG.X86_64 VG.Spec.Argon2 VG.Impl.Argon2.X86_64.DependentWord

theorem state_ok (s : State) (p : Params) (pass lane slice index : Nat)
    (h : FillKernel.Ready p pass lane slice index s) (state : FillState)
    (represented : Proof.Argon2.Represents s.mem (FillKernel.matrix s) p.blocks state.memory)
    (dependent : independent p pass slice = false) : WP isa code s fun t =>
      t.gpr .rdi = Proof.Argon2.FillStep.random p pass lane slice index state.memory ∧
      FillKernel.Ready p pass lane slice index t ∧
      Proof.Argon2.Represents t.mem (FillKernel.matrix t) p.blocks state.memory ∧
      Divide.Keeps ReferenceMap.changed s t := by
  refine (code_spec_ok s p pass lane slice index h state represented dependent).mono ?_
  rintro t ⟨random, keeps⟩
  refine ⟨random, h.of_keeps keeps, ?_, keeps⟩
  have base : FillKernel.matrix t = FillKernel.matrix s := by
    unfold FillKernel.matrix; rw [keeps.mem, keeps.regs .rbp (by decide)]
  rw [keeps.mem, base]; exact represented

end VG.Proof.Argon2.X86_64.DependentWord
end

/-! Both random sources satisfy the same filling-step postcondition. -/

namespace VG.Proof.Argon2.X86_64.RandomSource

open VG VG.X86_64 VG.Spec.Argon2

def writes (s : State) : List Region := AddressCache.writes s

structure Done (s t : State) (p : Params) (pass lane slice index : Nat) (state : FillState) : Prop where
  random : t.gpr .rdi = Proof.Argon2.FillStep.random p pass lane slice index state.memory
  ready : ∃ old, Ready p pass lane slice index old t
  represented : Proof.Argon2.Represents t.mem (FillKernel.matrix t) p.blocks state.memory
  regs : ∀ r ∈ calleeSaved, t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  frame : Frame (writes s) s.mem t.mem
  mxcsr : t.mxcsr = s.mxcsr

theorem Ready.index_nat {p : Params} {pass lane slice index old : Nat} {s : State}
    (h : Ready p pass lane slice index old s) : (s.gpr .r15).toNat = index := by
  rw [h.filling.position.index, ReferenceMap.word_nat index h.filling.bounds.index_bound64]

theorem independent_ok (s : State) (p : Params) (pass lane slice index old : Nat)
    (h : Ready p pass lane slice index old s) (state : FillState)
    (represented : Proof.Argon2.Represents s.mem (FillKernel.matrix s) p.blocks state.memory)
    (mode : independent p pass slice = true) :
    WP isa Impl.Argon2.X86_64.AddressCache.code s (Done s · p pass lane slice index state) := by
  refine (AddressCache.code_ok p pass lane slice old s h.cache.ready).mono ?_
  intro t done
  have base : FillKernel.matrix t = FillKernel.matrix s :=
    done.selected.frame_word h.cache.layout 232 (by decide) (by decide)
  have nextReady : Ready p pass lane slice index (AddressCache.wanted s) t := by
    refine ⟨done.selected.filling_ready h.cache.layout h.filling,
      done.selected.invariant h.cache.ready, ?_⟩
    rw [base, done.selected.work_eq]; exact h.matrixWork
  refine ⟨?_, ⟨_, nextReady⟩,
    done.selected.represents h.cache.layout h.filling h.matrixWork state.memory represented,
    done.selected.regs, done.selected.rd, done.selected.wr, done.selected.frame, done.selected.mxcsr⟩
  have random := done.random
  unfold AddressCache.wanted at random
  rw [h.index_nat] at random
  unfold Proof.Argon2.FillStep.random
  simp only [mode, ite_true]
  exact random

theorem dependent_ok (s : State) (p : Params) (pass lane slice index old : Nat)
    (h : Ready p pass lane slice index old s) (state : FillState)
    (represented : Proof.Argon2.Represents s.mem (FillKernel.matrix s) p.blocks state.memory)
    (mode : independent p pass slice = false) :
    WP isa Impl.Argon2.X86_64.DependentWord.code s (Done s · p pass lane slice index state) := by
  refine (DependentWord.state_ok s p pass lane slice index h.filling state represented mode).mono ?_
  rintro t ⟨random, _, matrix, keeps⟩
  refine ⟨random, ⟨old, h.of_keeps keeps⟩, matrix, ?_, keeps.rd, keeps.wr, ?_, keeps.mxcsr⟩
  · intro r hr
    apply keeps.regs
    simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  · rw [keeps.mem]; exact Frame.refl _ _

theorem code_ok (s : State) (p : Params) (pass lane slice index old : Nat)
    (h : Ready p pass lane slice index old s) (state : FillState)
    (represented : Proof.Argon2.Represents s.mem (FillKernel.matrix s) p.blocks state.memory) :
    WP isa Impl.Argon2.X86_64.RandomSource.code s (Done s · p pass lane slice index state) := by
  unfold Impl.Argon2.X86_64.RandomSource.code
  refine WP.seq ((prepare_ok s p pass lane slice index old h).mono ?_)
  rintro a ⟨flag, keeps⟩
  have next := h.of_keeps keeps
  have representedA : Proof.Argon2.Represents a.mem (FillKernel.matrix a) p.blocks state.memory := by
    have base : FillKernel.matrix a = FillKernel.matrix s := by
      unfold FillKernel.matrix; rw [keeps.mem, keeps.regs .rbp (by decide)]
    rw [base, keeps.mem]; exact represented
  have finish {t : State} (done : Done a t p pass lane slice index state) :
      Done s t p pass lane slice index state := by
    refine ⟨done.random, done.ready, done.represented, ?_, done.rd.trans keeps.rd,
      done.wr.trans keeps.wr, ?_, done.mxcsr.trans keeps.mxcsr⟩
    · intro r hr
      have ne : r ∉ ReferenceMap.changed := by
        simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
      exact (done.regs r hr).trans (keeps.regs r ne)
    · have frame := done.frame
      unfold writes AddressCache.writes AddressCalls.work at frame ⊢
      rw [keeps.mem, keeps.regs .rbp (by decide), keeps.regs .rsp (by decide)] at frame
      exact frame
  refine WP.ite (!independent p pass slice) (by simp only [eval, flag]) ?_ ?_
  · intro mode
    have dependent : independent p pass slice = false := by
      cases eq : independent p pass slice <;> simp_all
    exact (dependent_ok a p pass lane slice index old next state representedA dependent).mono
      (fun _ done => finish done)
  · intro mode
    have independent : independent p pass slice = true := by
      cases eq : independent p pass slice <;> simp_all
    exact (independent_ok a p pass lane slice index old next state representedA independent).mono
      (fun _ done => finish done)

end VG.Proof.Argon2.X86_64.RandomSource
