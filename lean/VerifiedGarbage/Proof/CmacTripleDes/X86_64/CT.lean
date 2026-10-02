import VerifiedGarbage.Proof.CmacTripleDes.X86_64.Lit
import VerifiedGarbage.Proof.CmacTripleDes.X86_64.Contract
import VerifiedGarbage.Proof.Framework.X86_64.Taint

/-!
# TDEA-CMAC on x86-64: constant time

Untrusted: everything here is checked by Lean. The taint analysis
(`Framework/X86_64/Taint.lean`) checks that only the arguments, which are
public, decide branches and addresses. `update` keeps the data pointer and
the blocks left in public slots of the scratch buffer, across the blocks'
stores of secrets at other offsets.
-/

namespace VG.Proof.CmacTripleDes.X86_64

open VG VG.X86_64

/-- `init`: the arguments are public; `rdx` and `rcx` point at the output and
the scratch buffer. -/
def τInit : X86_64.Taint.T :=
  { regs := .ofList [.rdi, .rsi, .rdx, .rcx, .rsp], flags := false, lens := [400, 640],
    bases := [(.rdx, 0, 0), (.rcx, 1, 0)] }

/-- `update`: the arguments are public; `rsi` and `r8` point at the state and
the scratch buffer. -/
def τUpdate : X86_64.Taint.T :=
  { regs := .ofList [.rdi, .rsi, .rdx, .rcx, .r8, .rsp], flags := false, lens := [8, 640],
    bases := [(.rsi, 0, 0), (.r8, 1, 0)] }

/-- `finalize`: the arguments are public; `rsi` and `r8` point at the state
and the scratch buffer. -/
def τFinalize : X86_64.Taint.T :=
  { regs := .ofList [.rdi, .rsi, .rdx, .rcx, .r8, .rsp], flags := false, lens := [8, 640],
    bases := [(.rsi, 0, 0), (.r8, 1, 0)] }

theorem init_agree {s₁ s₂ : State} (h₁ : initX86_64.pre s₁) (h₂ : initX86_64.pre s₂)
    (hpub : initX86_64.pub s₁ s₂) : X86_64.Taint.Agree τInit s₁ s₂ := by
  obtain ⟨p1, p2, p3, p4, p5⟩ := hpub
  have wf : ∀ s, initX86_64.pre s → X86_64.Taint.Wf τInit s := by
    intro s hs
    obtain ⟨-, hw, -, -, d3, -⟩ := hs
    refine ⟨fun _ => ⟨by simp [hw, τInit], by simp [hw, d3], by simp [hw]⟩, fun p hp => ?_⟩
    simp only [τInit, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl <;> simp [X86_64.Taint.region, hw]
  refine ⟨⟨fun r hr => ?_, fun h => by cases h⟩, fun _ => ?_, wf _ h₁, wf _ h₂, ?_, ?_, X86_64.Taint.noLo⟩
  · simp only [τInit, RegSet.mem_ofList, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> assumption
  · rw [h₁.2.1, h₂.2.1, p3, p4]
  · intro sl h; simp [τInit] at h
  · intro sl h; simp [τInit] at h

theorem update_agree {s₁ s₂ : State} (h₁ : updateX86_64.pre s₁) (h₂ : updateX86_64.pre s₂)
    (hpub : updateX86_64.pub s₁ s₂) : X86_64.Taint.Agree τUpdate s₁ s₂ := by
  obtain ⟨p1, p2, p3, p4, p5, p6⟩ := hpub
  have wf : ∀ s, updateX86_64.pre s → X86_64.Taint.Wf τUpdate s := by
    intro s hs
    obtain ⟨-, hw, -, -, -, -, d5, -⟩ := hs
    refine ⟨fun _ => ⟨by simp [hw, τUpdate], by simp [hw, d5], by simp [hw]⟩, fun p hp => ?_⟩
    simp only [τUpdate, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl <;> simp [X86_64.Taint.region, hw]
  refine ⟨⟨fun r hr => ?_, fun h => by cases h⟩, fun _ => ?_, wf _ h₁, wf _ h₂, ?_, ?_, X86_64.Taint.noLo⟩
  · simp only [τUpdate, RegSet.mem_ofList, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
  · rw [h₁.2.1, h₂.2.1, p2, p5]
  · intro sl h; simp [τUpdate] at h
  · intro sl h; simp [τUpdate] at h

theorem finalize_agree {s₁ s₂ : State} (h₁ : finalizeX86_64.pre s₁) (h₂ : finalizeX86_64.pre s₂)
    (hpub : finalizeX86_64.pub s₁ s₂) : X86_64.Taint.Agree τFinalize s₁ s₂ := by
  obtain ⟨p1, p2, p3, p4, p5, p6⟩ := hpub
  have wf : ∀ s, finalizeX86_64.pre s → X86_64.Taint.Wf τFinalize s := by
    intro s hs
    obtain ⟨-, hw, -, -, -, -, d5, -⟩ := hs
    refine ⟨fun _ => ⟨by simp [hw, τFinalize], by simp [hw, d5], by simp [hw]⟩, fun p hp => ?_⟩
    simp only [τFinalize, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl <;> simp [X86_64.Taint.region, hw]
  refine ⟨⟨fun r hr => ?_, fun h => by cases h⟩, fun _ => ?_, wf _ h₁, wf _ h₂, ?_, ?_, X86_64.Taint.noLo⟩
  · simp only [τFinalize, RegSet.mem_ofList, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
  · rw [h₁.2.1, h₂.2.1, p2, p5]
  · intro sl h; simp [τFinalize] at h
  · intro sl h; simp [τFinalize] at h

theorem update_ct : ConstantTime isa updateX86_64.pre updateX86_64.pub Impl.CmacTripleDes.X86_64.update :=
  VG.Taint.constantTime (A := taint) τUpdate (fun _ _ h₁ h₂ hp => update_agree h₁ h₂ hp) (by taint_decide)

theorem init_ct : ConstantTime isa initX86_64.pre initX86_64.pub Impl.CmacTripleDes.X86_64.init :=
  VG.Taint.constantTime (A := taint) τInit (fun _ _ h₁ h₂ hp => init_agree h₁ h₂ hp) (by taint_decide)

theorem finalize_ct :
    ConstantTime isa finalizeX86_64.pre finalizeX86_64.pub Impl.CmacTripleDes.X86_64.finalize :=
  VG.Taint.constantTime (A := taint) τFinalize (fun _ _ h₁ h₂ hp => finalize_agree h₁ h₂ hp)
    (by taint_decide)

end VG.Proof.CmacTripleDes.X86_64
