import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Scrypt.Arm.Salsa
import VerifiedGarbage.Proof.Scrypt.Arm.BlockMixVerified
import VerifiedGarbage.Proof.Scrypt.Arm.RoMixCT
import VerifiedGarbage.Spec.Scrypt.Contract

/-!
# scrypt on ARMv7: the shared contracts

Untrusted: everything here is checked by Lean. The proofs are written against
per-target contracts (`Proof/Scrypt/Arm/Contract.lean`); these theorems move
them to the shared contracts of `Spec/Scrypt/Contract.lean`, which the
artifacts are emitted with. The functions use no stack: `bl` leaves the
return address in `lr`, which each caller saves in its scratch space.
-/

namespace VG.Proof.Scrypt.Arm.Shared

theorem salsa :
    Verified Arm.target Impl.Scrypt.Arm.salsa (Spec.Scrypt.salsaContract Arm.abi) :=
  Proof.Scrypt.Arm.salsa_verified.of_implies (by
    contract_implies [Spec.Scrypt.salsaContract, Spec.Scrypt.salsaSig,
      Proof.Scrypt.salsaArm, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
      [Proof.Scrypt.Arm.satState] using Proof.Scrypt.Arm.satState)

theorem blockMix :
    Verified Arm.target Impl.Scrypt.Arm.blockMix (Spec.Scrypt.blockMixContract Arm.abi) :=
  Proof.Scrypt.Arm.BlockMix.blockMix_verified.of_implies
    { pre := by
        intro s h
        sig_unfold [Spec.Scrypt.blockMixContract, Spec.Scrypt.blockMixSig,
          Proof.Scrypt.blockMixArm, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val,
          Arm.State.addr] at h
        obtain ⟨hsp, hrd, hwr, ⟨⟨hby, hbs⟩, ⟨hys, hya⟩, hsa⟩, ⟨nb, ny, ns⟩, e, pos⟩ := h
        simp only [Proof.Scrypt.blockMixArm, Arm.State.addr]
        exact ⟨hrd, hwr, hys, hby, hbs, hya.symm, hsa.symm, nb, ny, by omega, by omega, e, pos⟩
      post := by
        implies_post [Spec.Scrypt.blockMixContract, Spec.Scrypt.blockMixSig,
          Proof.Scrypt.blockMixArm, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val,
          Arm.State.addr]
      pub := by
        implies_pub [Spec.Scrypt.blockMixContract, Spec.Scrypt.blockMixSig,
          Proof.Scrypt.blockMixArm, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val,
          Arm.State.addr]
      sat := by
        implies_sat [Spec.Scrypt.blockMixContract, Spec.Scrypt.blockMixSig,
          Proof.Scrypt.blockMixArm, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val,
          Arm.State.addr,
          Proof.Scrypt.Arm.BlockMix.bmSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read]
          using Proof.Scrypt.Arm.BlockMix.bmSat }

theorem roMix :
    Verified Arm.target Impl.Scrypt.Arm.roMix (Spec.Scrypt.roMixContract Arm.abi) :=
  Proof.Scrypt.Arm.RoMix.roMix_verified.of_implies
    { pre := by
        intro s h
        sig_unfold [Spec.Scrypt.roMixContract, Spec.Scrypt.roMixSig,
          Proof.Scrypt.roMixArm, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val,
          Arm.State.addr] at h
        obtain ⟨hsp, hrd, hwr, ⟨⟨hbv, hbs, hba⟩, ⟨hvs, hva⟩, hsa⟩, ⟨nb, nv, ns⟩, pos, md, pw, sl⟩ := h
        simp only [Proof.Scrypt.roMixArm, Arm.State.addr]
        exact ⟨hrd, hwr, hbv, hbs, hvs, hba.symm, hva.symm, hsa.symm, nb, nv, ns, by omega, pos, md,
          pw, sl⟩
      post := by
        implies_post [Spec.Scrypt.roMixContract, Spec.Scrypt.roMixSig,
          Proof.Scrypt.roMixArm, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val,
          Arm.State.addr]
      pub := by
        implies_pub [Spec.Scrypt.roMixContract, Spec.Scrypt.roMixSig,
          Proof.Scrypt.roMixArm, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val,
          Arm.State.addr]
      sat := by
        implies_sat [Spec.Scrypt.roMixContract, Spec.Scrypt.roMixSig,
          Proof.Scrypt.roMixArm, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val,
          Arm.State.addr,
          Proof.Scrypt.Arm.RoMix.satState, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read]
          using Proof.Scrypt.Arm.RoMix.satState }

end VG.Proof.Scrypt.Arm.Shared
