import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Poly1305.X86.Init
import VerifiedGarbage.Proof.Poly1305.X86.Blocks
import VerifiedGarbage.Proof.Poly1305.X86.Update
import VerifiedGarbage.Proof.Poly1305.X86.Finalize
import VerifiedGarbage.Spec.Poly1305.Contract

/-!
# Poly1305 on x86 (32-bit): the shared contracts

Untrusted: everything here is checked by Lean. The proofs are written against
per-target contracts (`Proof/Poly1305/X86/Contract.lean`); these theorems
move them to the shared contracts of `Spec/Poly1305/Contract.lean`, which the
artifacts are emitted with.
-/

namespace VG.Proof.Poly1305.X86.Shared

theorem init :
    Verified X86.target Impl.Poly1305.X86.init (Spec.Poly1305.initContract X86.abi) :=
  Proof.Poly1305.X86.init_verified.of_implies (by
    contract_implies [Spec.Poly1305.initContract, Spec.Poly1305.initSig, Proof.Poly1305.initX86,
      X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
      [Proof.Poly1305.X86.initSat, Proof.Poly1305.X86.initSatMem, X86.arg, X86.argAddr, Mem.readW,
        Mem.read] using Proof.Poly1305.X86.initSat)

theorem blocks :
    Verified X86.target Impl.Poly1305.X86.blocks (Spec.Poly1305.blocksContract X86.abi) :=
  Proof.Poly1305.X86.blocks_verified.of_implies (by
    contract_implies [Spec.Poly1305.blocksContract, Spec.Poly1305.blocksSig, Proof.Poly1305.blocksX86,
      X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
      [Proof.Poly1305.X86.blocksSat, Proof.Poly1305.X86.blocksSatMem, X86.arg, X86.argAddr, Mem.readW,
        Mem.read] using Proof.Poly1305.X86.blocksSat)

theorem update :
    Verified X86.target Impl.Poly1305.X86.update (Spec.Poly1305.updateContract X86.abi) :=
  Proof.Poly1305.X86.update_verified.of_implies (by
    contract_implies [Spec.Poly1305.updateContract, Spec.Poly1305.updateSig, Proof.Poly1305.updateX86,
      Proof.Poly1305.countX86, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
      [Proof.Poly1305.X86.updateSat, Proof.Poly1305.X86.updateSatMem, X86.arg, X86.argAddr, Mem.readW,
        Mem.read] using Proof.Poly1305.X86.updateSat)

/-- The per-target contract of `finalize` only needs the length of the
message modulo 16. -/
theorem finalize :
    Verified X86.target Impl.Poly1305.X86.finalize (Spec.Poly1305.finalizeContract X86.abi) :=
  Proof.Poly1305.X86.finalize_verified.of_implies
    { pre := by
        implies_pre [Spec.Poly1305.finalizeContract, Spec.Poly1305.finalizeSig,
          Proof.Poly1305.finalizeX86, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
      post := by
        intro s s' _ h
        sig_unfold [Spec.Poly1305.finalizeContract, Spec.Poly1305.finalizeSig, X86.abi, X86.argSlots,
          X86.argVal, X86.argBytes]
        intro key msg hb hc
        exact h key msg hb (Proof.Poly1305.X86.count_mod16 hc)
      pub := by
        implies_pub [Spec.Poly1305.finalizeContract, Spec.Poly1305.finalizeSig,
          Proof.Poly1305.finalizeX86, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
      sat := by
        implies_sat [Spec.Poly1305.finalizeContract, Spec.Poly1305.finalizeSig,
          Proof.Poly1305.finalizeX86, X86.abi, X86.argSlots, X86.argVal, X86.argBytes,
          Proof.Poly1305.X86.finalizeSat, Proof.Poly1305.X86.finalizeSatMem, X86.arg, X86.argAddr,
          Mem.readW, Mem.read] using Proof.Poly1305.X86.finalizeSat }

end VG.Proof.Poly1305.X86.Shared
