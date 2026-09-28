import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Poly1305.X86_64.Init
import VerifiedGarbage.Proof.Poly1305.X86_64.Finalize
import VerifiedGarbage.Spec.Poly1305.Contract

/-!
# Poly1305 on x86-64: the shared contracts

Untrusted: everything here is checked by Lean. The proofs are written against
per-target contracts (`Proof/Poly1305/X86_64/Contract.lean`); these theorems
move them to the shared contracts of `Spec/Poly1305/Contract.lean`, which the
artifacts are emitted with.
-/

namespace VG.Proof.Poly1305.X86_64.Shared

theorem init :
    Verified X86_64.target Impl.Poly1305.X86_64.init (Spec.Poly1305.initContract X86_64.abi) :=
  Proof.Poly1305.X86_64.init_verified.of_implies (by
    contract_implies [Spec.Poly1305.initContract, Spec.Poly1305.initSig,
      Proof.Poly1305.initX86_64, X86_64.abi, X86_64.argRegs]
      [Proof.Poly1305.X86_64.initSat] using Proof.Poly1305.X86_64.initSat)

theorem blocks :
    Verified X86_64.target Impl.Poly1305.X86_64.blocks (Spec.Poly1305.blocksContract X86_64.abi) :=
  Proof.Poly1305.X86_64.blocks_verified.of_implies (by
    contract_implies [Spec.Poly1305.blocksContract, Spec.Poly1305.blocksSig,
      Proof.Poly1305.blocksX86_64, X86_64.abi, X86_64.argRegs]
      [Proof.Poly1305.X86_64.blocksSat] using Proof.Poly1305.X86_64.blocksSat)

theorem finalize :
    Verified X86_64.target Impl.Poly1305.X86_64.finalize (Spec.Poly1305.finalizeContract X86_64.abi) :=
  Proof.Poly1305.X86_64.finalize_verified.of_implies (by
    contract_implies [Spec.Poly1305.finalizeContract, Spec.Poly1305.finalizeSig,
      Proof.Poly1305.finalizeX86_64, X86_64.abi, X86_64.argRegs]
      [Proof.Poly1305.X86_64.finalizeSat] using Proof.Poly1305.X86_64.finalizeSat)

end VG.Proof.Poly1305.X86_64.Shared
