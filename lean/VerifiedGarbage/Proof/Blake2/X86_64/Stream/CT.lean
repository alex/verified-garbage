import VerifiedGarbage.Proof.Blake2.X86_64.Stream.Lit
import VerifiedGarbage.Proof.Blake2.X86_64.Stream.Common
import VerifiedGarbage.Proof.Framework.X86_64.Taint

/-!
# Streaming BLAKE2 on x86-64: constant time

Untrusted: everything here is checked by Lean. The taint analysis of `init`,
`update` and `finalize` (the compression function they call included), from
the public arguments: the pointers, `outlen`, `keylen`, `count` and `len`.
-/

namespace VG.Proof.Blake2.X86_64.Stream

open VG VG.X86_64 VG.Spec.Blake2

section
variable (w : Nat)

/-- `init` (which makes no calls): the arguments are public; `rdi` points at
the state. -/
def τInit : X86_64.Taint.T :=
  { regs := .ofList [.rdi, .rsi, .rdx, .rcx], flags := false, lens := [bufOff w + blockBytes w],
    bases := [(.rdi, 0, 0)] }

/-- `update`: the arguments are public; `rdi` and `r8` point at the state and
the scratch space. -/
def τUpdate : X86_64.Taint.T :=
  { regs := .ofList [.rdi, .rsi, .rdx, .rcx, .r8, .rsp], flags := false,
    lens := [bufOff w + blockBytes w, 576], bases := [(.rdi, 0, 0), (.r8, 1, 0)] }

/-- `finalize`: the arguments are public; `rdi`, `rdx` and `rcx` point at the
state, the output and the scratch space. -/
def τFinalize : X86_64.Taint.T :=
  { regs := .ofList [.rdi, .rsi, .rdx, .rcx, .rsp], flags := false,
    lens := [bufOff w + blockBytes w, bufOff w, 576],
    bases := [(.rdi, 0, 0), (.rdx, 1, 0), (.rcx, 2, 0)] }

end

variable {w : Nat} {P : Params w}

theorem init_agree (hP : Ok P) {s₁ s₂ : State} (h₁ : (initX86_64 P).pre s₁) (h₂ : (initX86_64 P).pre s₂)
    (hpub : (initX86_64 P).pub s₁ s₂) : X86_64.Taint.Agree (τInit w) s₁ s₂ := by
  obtain ⟨p1, p2, p3, p4⟩ := hpub
  have wf : ∀ s, (initX86_64 P).pre s → X86_64.Taint.Wf (τInit w) s := by
    intro s hs
    obtain ⟨-, hw, -⟩ := hs
    refine ⟨fun _ => ⟨by simp [hw, τInit], by simp [hw], by simp [hw]; rcases hP.w with rfl | rfl <;> decide⟩, fun p hp => ?_⟩
    simp only [τInit, List.mem_cons, List.not_mem_nil, or_false] at hp
    subst hp; simp [X86_64.Taint.region, hw]
  refine ⟨⟨fun r hr => ?_, fun h => by cases h⟩, fun _ => ?_, wf _ h₁, wf _ h₂, ?_, ?_,
    X86_64.Taint.noLo⟩
  · simp only [τInit, RegSet.mem_ofList, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> assumption
  · rw [h₁.2.1, h₂.2.1, p1]
  · intro sl h; simp [τInit] at h
  · intro sl h; simp [τInit] at h

theorem update_agree (hP : Ok P) {s₁ s₂ : State} (h₁ : (updateX86_64 P).pre s₁)
    (h₂ : (updateX86_64 P).pre s₂) (hpub : (updateX86_64 P).pub s₁ s₂) :
    X86_64.Taint.Agree (τUpdate w) s₁ s₂ := by
  obtain ⟨p1, p2, p3, p4, p5, p6⟩ := hpub
  have wf : ∀ s, (updateX86_64 P).pre s → X86_64.Taint.Wf (τUpdate w) s := by
    intro s hs
    obtain ⟨-, hw, hd, -⟩ := hs
    refine ⟨fun _ => ⟨by simp [hw, τUpdate], by simp [hw, hd], by
      simp [hw]; rcases hP.w with rfl | rfl <;> decide⟩, fun p hp => ?_⟩
    simp only [τUpdate, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl <;> simp [X86_64.Taint.region, hw]
  refine ⟨⟨fun r hr => ?_, fun h => by cases h⟩, fun _ => ?_, wf _ h₁, wf _ h₂, ?_, ?_,
    X86_64.Taint.noLo⟩
  · simp only [τUpdate, RegSet.mem_ofList, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
  · rw [h₁.2.1, h₂.2.1, p1, p5]
  · intro sl h; simp [τUpdate] at h
  · intro sl h; simp [τUpdate] at h

theorem finalize_agree (hP : Ok P) {s₁ s₂ : State} (h₁ : (finalizeX86_64 P).pre s₁)
    (h₂ : (finalizeX86_64 P).pre s₂) (hpub : (finalizeX86_64 P).pub s₁ s₂) :
    X86_64.Taint.Agree (τFinalize w) s₁ s₂ := by
  obtain ⟨p1, p2, p3, p4, p5⟩ := hpub
  have wf : ∀ s, (finalizeX86_64 P).pre s → X86_64.Taint.Wf (τFinalize w) s := by
    intro s hs
    obtain ⟨-, hw, d1, d2, d3, -⟩ := hs
    refine ⟨fun _ => ⟨by simp [hw, τFinalize], by simp [hw, d1, d2, d3], by
      simp [hw]; rcases hP.w with rfl | rfl <;> decide⟩, fun p hp => ?_⟩
    simp only [τFinalize, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl <;> simp [X86_64.Taint.region, hw]
  refine ⟨⟨fun r hr => ?_, fun h => by cases h⟩, fun _ => ?_, wf _ h₁, wf _ h₂, ?_, ?_,
    X86_64.Taint.noLo⟩
  · simp only [τFinalize, RegSet.mem_ofList, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> assumption
  · rw [h₁.2.1, h₂.2.1, p1, p3, p4]
  · intro sl h; simp [τFinalize] at h
  · intro sl h; simp [τFinalize] at h

theorem okB : Ok Spec.Blake2.b := ⟨by decide, .inl rfl⟩
theorem okS : Ok Spec.Blake2.s := ⟨by decide, .inr rfl⟩

theorem initB_ct : ConstantTime isa (initX86_64 b).pre (initX86_64 b).pub
    (Impl.Blake2.X86_64.Stream.init b) :=
  VG.Taint.constantTime (A := taint) (τInit 64) (fun _ _ h₁ h₂ hp => init_agree okB h₁ h₂ hp)
    (by taint_decide)

theorem initS_ct : ConstantTime isa (initX86_64 s).pre (initX86_64 s).pub
    (Impl.Blake2.X86_64.Stream.init s) :=
  VG.Taint.constantTime (A := taint) (τInit 32) (fun _ _ h₁ h₂ hp => init_agree okS h₁ h₂ hp)
    (by taint_decide)

theorem updateB_ct : ConstantTime isa (updateX86_64 b).pre (updateX86_64 b).pub
    (Impl.Blake2.X86_64.Stream.update b) :=
  VG.Taint.constantTime (A := taint) (τUpdate 64) (fun _ _ h₁ h₂ hp => update_agree okB h₁ h₂ hp)
    (by taint_decide)

theorem updateS_ct : ConstantTime isa (updateX86_64 s).pre (updateX86_64 s).pub
    (Impl.Blake2.X86_64.Stream.update s) :=
  VG.Taint.constantTime (A := taint) (τUpdate 32) (fun _ _ h₁ h₂ hp => update_agree okS h₁ h₂ hp)
    (by taint_decide)

theorem finalizeB_ct : ConstantTime isa (finalizeX86_64 b).pre (finalizeX86_64 b).pub
    (Impl.Blake2.X86_64.Stream.finalize b) :=
  VG.Taint.constantTime (A := taint) (τFinalize 64)
    (fun _ _ h₁ h₂ hp => finalize_agree okB h₁ h₂ hp) (by taint_decide)

theorem finalizeS_ct : ConstantTime isa (finalizeX86_64 s).pre (finalizeX86_64 s).pub
    (Impl.Blake2.X86_64.Stream.finalize s) :=
  VG.Taint.constantTime (A := taint) (τFinalize 32)
    (fun _ _ h₁ h₂ hp => finalize_agree okS h₁ h₂ hp) (by taint_decide)

end VG.Proof.Blake2.X86_64.Stream
