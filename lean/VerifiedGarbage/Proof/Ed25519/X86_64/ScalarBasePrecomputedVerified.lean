import VerifiedGarbage.Proof.Ed25519.X86_64.ScalarBasePrecomputedCT
import VerifiedGarbage.Proof.Ed25519.X86_64.ScalarBaseVerified

/-! The precomputed variant satisfies the same reviewed ABI contract. -/
namespace VG.Proof.Ed25519.X86_64
open VG VG.X86_64 VG.Impl.Ed25519.X86_64

theorem scalarBase_precomputed_ok (s : State) (hs : scalarBaseLocal.pre s) :
    ∃ t s', Exec isa scalarBase_precomputed s t s' ∧
      abiPreserved s s' ∧ scalarBaseLocal.post s s' := by
  obtain ⟨t, s', he, h⟩ := scalarBase_correct_of_engine scalarBasePrecomputedEngine
    scalarBasePrecomputedEngine_ok hs
  exact ⟨t, s', he, abiPreserved_of_exec (by lit_decide) he h.1, h.2⟩

theorem scalarBase_precomputed_verified : Verified X86_64.target scalarBase_precomputed
    (Spec.Ed25519.scalarBaseContract X86_64.abi) :=
  Verified.of_correct scalarBase_precomputed_ok scalarBase_precomputed_ct (by
    sig_implies [Spec.Ed25519.scalarBaseContract, Spec.Ed25519.scalarBaseSig,
      Spec.Ed25519.scratchWords, X86_64.abi, X86_64.argRegs, scalarBaseLocal]
      [baseSatState] using baseSatState)

end VG.Proof.Ed25519.X86_64
