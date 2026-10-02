import VerifiedGarbage.Proof.Ed25519.X86_64.MulAddMain
import VerifiedGarbage.Proof.Ed25519.X86_64.MulAddLit
import VerifiedGarbage.Proof.Framework.Contract

/-! Untrusted: scalar multiply-add satisfies the merged Ed25519 contract. -/

namespace VG.Proof.Ed25519.X86_64

open VG VG.X86_64 VG.Impl.Ed25519.X86_64

def mulAddSatState : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 0x2000 | .rdx => 0x3000 | .rcx => 0x4000
    | .r8 => 0x5000 | .rsp => 0x9000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x2000, 32⟩, ⟨0x3000, 32⟩, ⟨0x4000, 32⟩]
  wr := [⟨0x1000, 32⟩, ⟨0x5000, 8192⟩]

theorem scalarMulAdd_ok (s : State) (hs : scalarMulAddLocal.pre s) :
    ∃ t s', Exec isa scalarMulAdd s t s' ∧ abiPreserved s s' ∧ scalarMulAddLocal.post s s' := by
  obtain ⟨t, s', he, h⟩ := scalarMulAdd_correct (MulAddPre.of hs)
  exact ⟨t, s', he, abiPreserved_of_exec (by lit_decide) he h.1, h.2⟩

/-- The arguments are public, and so is what the code stores at `r8` (region 1),
the scratch: the output's address, at byte 48. -/
def scalarMulAddτ : X86_64.Taint.T :=
  { regs := .ofList [.rdi, .rsi, .rdx, .rcx, .r8], flags := false, lens := [0, 8192],
    bases := [(.r8, 1, 0)] }

theorem scalarMulAdd_agree {s₁ s₂ : State} (h₁ : scalarMulAddLocal.pre s₁)
    (h₂ : scalarMulAddLocal.pre s₂) (hpub : scalarMulAddLocal.pub s₁ s₂) :
    X86_64.Taint.Agree scalarMulAddτ s₁ s₂ := by
  obtain ⟨-, p1, p2, p3, p4, p5⟩ := hpub
  have wf : ∀ s, scalarMulAddLocal.pre s → X86_64.Taint.Wf scalarMulAddτ s := by
    intro s hs
    obtain ⟨-, hw, -, -, -, -, -, -, d⟩ := hs
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

theorem scalarMulAdd_ct : ConstantTime isa scalarMulAddLocal.pre scalarMulAddLocal.pub scalarMulAdd := by
  refine VG.Taint.constantTime (A := taint) scalarMulAddτ
    (fun _ _ h₁ h₂ hp => scalarMulAdd_agree h₁ h₂ hp) (by taint_decide)

theorem scalarMulAdd_verified : Verified X86_64.target scalarMulAdd
    (Spec.Ed25519.scalarMulAddContract X86_64.abi) :=
  Verified.of_correct scalarMulAdd_ok scalarMulAdd_ct (by
    sig_implies [Spec.Ed25519.scalarMulAddContract, Spec.Ed25519.scalarMulAddSig,
      Spec.Ed25519.scratchWords, X86_64.abi, X86_64.argRegs, scalarMulAddLocal]
      [mulAddSatState] using mulAddSatState)

end VG.Proof.Ed25519.X86_64
