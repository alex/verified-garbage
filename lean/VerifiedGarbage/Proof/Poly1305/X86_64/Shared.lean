import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Poly1305.X86_64.Init
import VerifiedGarbage.Proof.Poly1305.X86_64.Finalize
import VerifiedGarbage.Proof.Poly1305.X86_64.Update
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

/-- The per-target contracts of `update` and `finalize` only need the length
of the message modulo 16. -/
theorem count_mod {count : BitVec 64} {n : Nat} (h : count = BitVec.ofNat 64 n) :
    count.toNat % 16 = n % 16 := by
  rw [h, BitVec.toNat_ofNat]; omega

theorem update :
    Verified X86_64.target Impl.Poly1305.X86_64.update (Spec.Poly1305.updateContract X86_64.abi) :=
  Proof.Poly1305.X86_64.update_verified.of_implies
    { pre := by
        implies_pre [Spec.Poly1305.updateContract, Spec.Poly1305.updateSig,
          Proof.Poly1305.updateX86_64, X86_64.abi, X86_64.argRegs]
      post := by
        intro s s' _ h
        sig_unfold [Spec.Poly1305.updateContract, Spec.Poly1305.updateSig, X86_64.abi, X86_64.argRegs]
        intro key msg hb hc
        exact h key msg hb (count_mod hc)
      pub := by
        implies_pub [Spec.Poly1305.updateContract, Spec.Poly1305.updateSig,
          Proof.Poly1305.updateX86_64, X86_64.abi, X86_64.argRegs]
      sat := by
        implies_sat [Spec.Poly1305.updateContract, Spec.Poly1305.updateSig, X86_64.abi, X86_64.argRegs,
          Proof.Poly1305.X86_64.updateSat] using Proof.Poly1305.X86_64.updateSat }

theorem finalize :
    Verified X86_64.target Impl.Poly1305.X86_64.finalize (Spec.Poly1305.finalizeContract X86_64.abi) :=
  Proof.Poly1305.X86_64.finalize_verified.of_implies
    { pre := by
        implies_pre [Spec.Poly1305.finalizeContract, Spec.Poly1305.finalizeSig,
          Proof.Poly1305.finalizeX86_64, X86_64.abi, X86_64.argRegs]
      post := by
        intro s s' _ h
        sig_unfold [Spec.Poly1305.finalizeContract, Spec.Poly1305.finalizeSig, X86_64.abi, X86_64.argRegs]
        intro key msg hb hc
        exact h.2 key msg hb (count_mod hc)
      pub := by
        implies_pub [Spec.Poly1305.finalizeContract, Spec.Poly1305.finalizeSig,
          Proof.Poly1305.finalizeX86_64, X86_64.abi, X86_64.argRegs]
      sat := by
        implies_sat [Spec.Poly1305.finalizeContract, Spec.Poly1305.finalizeSig, X86_64.abi, X86_64.argRegs,
          Proof.Poly1305.X86_64.finalizeSat] using Proof.Poly1305.X86_64.finalizeSat }

end VG.Proof.Poly1305.X86_64.Shared
