import VerifiedGarbage.Proof.Ed25519.X86_64.ScalarMain
import VerifiedGarbage.Proof.Ed25519.X86_64.ScalarLit
import VerifiedGarbage.Proof.Framework.Contract

/-!
# Scalar reduction: the merged contract

Untrusted. Correctness includes the ABI. Taint analysis checks that secret
input bytes never determine branches or memory addresses. A concrete
witness proves the signature contract is satisfiable.
-/

namespace VG.Proof.Ed25519.X86_64

open VG VG.X86_64 VG.Impl.Ed25519.X86_64

def scalarSatState : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 0x2000 | .rdx => 0x3000 | .rsp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x2000, 64⟩]
  wr := [⟨0x1000, 32⟩, ⟨0x3000, 8192⟩]

theorem scalarReduce_ok (s : State) (hs : scalarReduceLocal.pre s) :
    ∃ t s', Exec isa scalarReduce s t s' ∧ abiPreserved s s' ∧ scalarReduceLocal.post s s' := by
  obtain ⟨t, s', he, h⟩ := scalarReduce_correct hs
  exact ⟨t, s', he, abiPreserved_of_exec (by lit_decide) he h.1, h.2⟩

theorem scalarReduce_ct : ConstantTime isa scalarReduceLocal.pre scalarReduceLocal.pub scalarReduce := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.rdi, .rsi, .rdx]) ?_
    (by taint_decide)
  intro s₁ s₂ _ _ ⟨_, h1, h2, h3⟩
  refine Taint.agree_ofRegs fun r hr => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl <;> assumption

theorem scalarReduce_verified : Verified X86_64.target scalarReduce
    (Spec.Ed25519.scalarReduceContract X86_64.abi) :=
  Verified.of_correct scalarReduce_ok scalarReduce_ct (by
    sig_implies [Spec.Ed25519.scalarReduceContract, Spec.Ed25519.scalarReduceSig,
      Spec.Ed25519.scratchWords, X86_64.abi, X86_64.argRegs, scalarReduceLocal]
      [scalarSatState] using scalarSatState)

end VG.Proof.Ed25519.X86_64
