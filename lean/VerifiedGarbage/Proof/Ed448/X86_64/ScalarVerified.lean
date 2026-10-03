import VerifiedGarbage.Proof.Ed448.X86_64.ScalarMulAddMain
import VerifiedGarbage.Proof.Ed448.X86_64.ScalarLit
import VerifiedGarbage.Proof.Framework.X86_64.Taint
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Spec.Ed448.Contract

/-!
# Ed448 scalar arithmetic on x86-64: `Verified`

Correctness includes the ABI. Taint analysis checks that secret input bytes
never determine branches or memory addresses. A concrete witness proves the
signature contract is satisfiable.
-/

namespace VG.Proof.Ed448.X86_64

open VG VG.X86_64 VG.Impl.Ed448.X86_64

def scalarReduceSat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 0x2000 | .rdx => 0x3000 | .rsp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x2000, 114⟩]
  wr := [⟨0x1000, 57⟩, ⟨0x3000, 8192⟩]

theorem scalarReduce_ok (s : State) (hs : scalarReduceLocal.pre s) :
    ∃ t s', Exec isa scalarReduce s t s' ∧ abiPreserved s s' ∧ scalarReduceLocal.post s s' := by
  obtain ⟨t, s', he, h⟩ := scalarReduce_correct hs
  exact ⟨t, s', he, abiPreserved_of_exec (by lit_decide) he h.1, h.2⟩

/-- The arguments are public, and so is what the code stores in the working
space (writable region 1, at `rdx`): the output's address, at `OUT`. -/
def scalarReduceτ : X86_64.Taint.T :=
  { regs := .ofList [.rdi, .rsi, .rdx], flags := false, lens := [0, 8192], bases := [(.rdx, 1, 0)] }

theorem scalarReduce_agree {s₁ s₂ : State} (h₁ : scalarReduceLocal.pre s₁)
    (h₂ : scalarReduceLocal.pre s₂) (hpub : scalarReduceLocal.pub s₁ s₂) :
    X86_64.Taint.Agree scalarReduceτ s₁ s₂ := by
  obtain ⟨-, p1, p2, p3⟩ := hpub
  have wf : ∀ s, scalarReduceLocal.pre s → X86_64.Taint.Wf scalarReduceτ s := by
    intro s hs
    obtain ⟨-, hw, -, -, -, d, -⟩ := hs
    refine ⟨fun _ => ⟨by simp [hw, scalarReduceτ], by simp [hw, d], by simp [hw]⟩, fun p hp => ?_⟩
    simp only [scalarReduceτ, List.mem_cons, List.not_mem_nil, or_false] at hp
    subst hp; simp [X86_64.Taint.region, hw]
  refine ⟨⟨fun r hr => ?_, fun h => by cases h⟩, fun _ => ?_, wf _ h₁, wf _ h₂, ?_, ?_,
    X86_64.Taint.noLo⟩
  · simp only [scalarReduceτ, RegSet.mem_ofList, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> assumption
  · rw [h₁.2.1, h₂.2.1, p1, p3]
  · intro sl h; simp [scalarReduceτ] at h
  · intro sl h; simp [scalarReduceτ] at h

theorem scalarReduce_ct :
    ConstantTime isa scalarReduceLocal.pre scalarReduceLocal.pub scalarReduce := by
  refine VG.Taint.constantTime (A := taint) scalarReduceτ
    (fun _ _ h₁ h₂ hp => scalarReduce_agree h₁ h₂ hp) (by taint_decide)

theorem scalarReduce_verified : Verified X86_64.target scalarReduce
    (Spec.Ed448.scalarReduceContract X86_64.abi) :=
  Verified.of_correct scalarReduce_ok scalarReduce_ct (by
    sig_implies [Spec.Ed448.scalarReduceContract, Spec.Ed448.scalarReduceSig,
      Spec.Ed448.scratchWords, X86_64.abi, X86_64.argRegs, scalarReduceLocal]
      [scalarReduceSat] using scalarReduceSat)

def scalarMulAddSat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 0x2000 | .rdx => 0x3000 | .rcx => 0x4000 | .r8 => 0x5000
    | .rsp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x2000, 57⟩, ⟨0x3000, 57⟩, ⟨0x4000, 57⟩]
  wr := [⟨0x1000, 57⟩, ⟨0x5000, 8192⟩]

theorem scalarMulAdd_ok (s : State) (hs : scalarMulAddLocal.pre s) :
    ∃ t s', Exec isa scalarMulAdd s t s' ∧ abiPreserved s s' ∧ scalarMulAddLocal.post s s' := by
  obtain ⟨t, s', he, h⟩ := scalarMulAdd_correct hs
  exact ⟨t, s', he, abiPreserved_of_exec (by lit_decide) he h.1, h.2⟩

/-- The arguments are public, and so is what the code stores in the working
space (writable region 1, at `r8`): the output's and inputs' addresses. -/
def scalarMulAddτ : X86_64.Taint.T :=
  { regs := .ofList [.rdi, .rsi, .rdx, .rcx, .r8], flags := false, lens := [0, 8192],
    bases := [(.r8, 1, 0)] }

theorem scalarMulAdd_agree {s₁ s₂ : State} (h₁ : scalarMulAddLocal.pre s₁)
    (h₂ : scalarMulAddLocal.pre s₂) (hpub : scalarMulAddLocal.pub s₁ s₂) :
    X86_64.Taint.Agree scalarMulAddτ s₁ s₂ := by
  obtain ⟨-, p1, p2, p3, p4, p5⟩ := hpub
  have wf : ∀ s, scalarMulAddLocal.pre s → X86_64.Taint.Wf scalarMulAddτ s := by
    intro s hs
    obtain ⟨-, hw, -, -, -, -, -, d, -⟩ := hs
    refine ⟨fun _ => ⟨by simp [hw, scalarMulAddτ], by simp [hw, d], by simp [hw]⟩, fun p hp => ?_⟩
    simp only [scalarMulAddτ, List.mem_cons, List.not_mem_nil, or_false] at hp
    subst hp; simp [X86_64.Taint.region, hw]
  refine ⟨⟨fun r hr => ?_, fun h => by cases h⟩, fun _ => ?_, wf _ h₁, wf _ h₂, ?_, ?_,
    X86_64.Taint.noLo⟩
  · simp only [scalarMulAddτ, RegSet.mem_ofList, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> assumption
  · rw [h₁.2.1, h₂.2.1, p1, p5]
  · intro sl h; simp [scalarMulAddτ] at h
  · intro sl h; simp [scalarMulAddτ] at h

theorem scalarMulAdd_ct :
    ConstantTime isa scalarMulAddLocal.pre scalarMulAddLocal.pub scalarMulAdd := by
  refine VG.Taint.constantTime (A := taint) scalarMulAddτ
    (fun _ _ h₁ h₂ hp => scalarMulAdd_agree h₁ h₂ hp) (by taint_decide)

theorem scalarMulAdd_verified : Verified X86_64.target scalarMulAdd
    (Spec.Ed448.scalarMulAddContract X86_64.abi) :=
  Verified.of_correct scalarMulAdd_ok scalarMulAdd_ct (by
    sig_implies [Spec.Ed448.scalarMulAddContract, Spec.Ed448.scalarMulAddSig,
      Spec.Ed448.scratchWords, X86_64.abi, X86_64.argRegs, scalarMulAddLocal]
      [scalarMulAddSat] using scalarMulAddSat)

end VG.Proof.Ed448.X86_64
