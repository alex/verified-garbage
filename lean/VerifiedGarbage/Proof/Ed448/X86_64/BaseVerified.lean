import VerifiedGarbage.Proof.Ed448.X86_64.BaseMain
import VerifiedGarbage.Proof.Ed448.X86_64.BaseLit
import VerifiedGarbage.Proof.Framework.X86_64.Taint
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Spec.Ed448.Contract

/-!
# Ed448 base-point multiplication on x86-64: `Verified`

Correctness including the ABI, constant time
(by taint tracking: the only branches are on the loop counters, and every
address is an argument plus a constant or a counter), and a concrete state
satisfying the signature's contract.
-/

namespace VG.Proof.Ed448.X86_64

open VG VG.X86_64 VG.Impl.Ed448.X86_64

def scalarBaseSat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 0x2000 | .rdx => 0x3000 | .rsp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x2000, 57⟩]
  wr := [⟨0x1000, 57⟩, ⟨0x3000, 8192⟩]

/-- The arguments are public, and so is what the code stores in the working
space (writable region 1, at `rdx`): the output's address, at `OUT`. -/
def scalarBaseτ : X86_64.Taint.T :=
  { regs := .ofList [.rdi, .rsi, .rdx], flags := false, lens := [0, 8192], bases := [(.rdx, 1, 0)] }

theorem scalarBase_agree {s₁ s₂ : State} (h₁ : scalarBaseLocal.pre s₁)
    (h₂ : scalarBaseLocal.pre s₂) (hpub : scalarBaseLocal.pub s₁ s₂) :
    X86_64.Taint.Agree scalarBaseτ s₁ s₂ := by
  obtain ⟨-, p1, p2, p3⟩ := hpub
  have wf : ∀ s, scalarBaseLocal.pre s → X86_64.Taint.Wf scalarBaseτ s := by
    intro s hs
    obtain ⟨-, hw, -, -, -, d, -⟩ := hs
    refine ⟨fun _ => ⟨by simp [hw, scalarBaseτ], by simp [hw, d], by simp [hw]⟩, fun p hp => ?_⟩
    simp only [scalarBaseτ, List.mem_cons, List.not_mem_nil, or_false] at hp
    subst hp; simp [X86_64.Taint.region, hw]
  refine ⟨⟨fun r hr => ?_, fun h => by cases h⟩, fun _ => ?_, wf _ h₁, wf _ h₂, ?_, ?_,
    X86_64.Taint.noLo⟩
  · simp only [scalarBaseτ, RegSet.mem_ofList, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> assumption
  · rw [h₁.2.1, h₂.2.1, p1, p3]
  · intro sl h; simp [scalarBaseτ] at h
  · intro sl h; simp [scalarBaseτ] at h

theorem scalarBase_ok (s : State) (hs : scalarBaseLocal.pre s) :
    ∃ t s', Exec isa scalarBase s t s' ∧ abiPreserved s s' ∧ scalarBaseLocal.post s s' := by
  obtain ⟨t, s', he, h⟩ := scalarBase_correct Proof.X448.X86_64.baseline_ok hs
  exact ⟨t, s', he, abiPreserved_of_exec (by lit_decide) he h.1, h.2⟩

theorem scalarBase_ct : ConstantTime isa scalarBaseLocal.pre scalarBaseLocal.pub scalarBase := by
  refine VG.Taint.constantTime (A := taint) scalarBaseτ
    (fun _ _ h₁ h₂ hp => scalarBase_agree h₁ h₂ hp) (by taint_decide)

theorem scalarBase_verified : Verified X86_64.target scalarBase
    (Spec.Ed448.scalarBaseContract X86_64.abi) :=
  Verified.of_correct scalarBase_ok scalarBase_ct (by
    sig_implies [Spec.Ed448.scalarBaseContract, Spec.Ed448.scalarBaseSig,
      Spec.Ed448.scratchWords, X86_64.abi, X86_64.argRegs, scalarBaseLocal]
      [scalarBaseSat] using scalarBaseSat)

end VG.Proof.Ed448.X86_64
