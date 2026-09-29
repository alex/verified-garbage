import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.ChaCha20Poly1305.Arm.Verified
import VerifiedGarbage.Spec.ChaCha20Poly1305.Contract

/-!
# ChaCha20-Poly1305 on ARMv7: the shared contracts

Untrusted: everything here is checked by Lean. The proofs are written against
per-target contracts (`Proof/ChaCha20Poly1305/Arm/Contract.lean`); these
theorems move them to the shared contracts of
`Spec/ChaCha20Poly1305/Contract.lean`, which the artifacts are emitted with.
The functions use 8 bytes of stack: the frame that passes the stack
arguments of `vg_poly1305_finalize`. Their calls (`bl`) store their return
addresses in `lr`, which they save in the context.
-/

namespace VG.Proof.ChaCha20Poly1305.Arm.Shared

theorem «seal» :
    Verified Arm.target Impl.ChaCha20Poly1305.Arm.«seal» (Spec.ChaCha20Poly1305.sealContract Arm.abi 8) :=
  Proof.ChaCha20Poly1305.Arm.seal_verified.of_implies (by
    contract_implies [Spec.ChaCha20Poly1305.sealContract, Spec.ChaCha20Poly1305.sealSig,
      Proof.ChaCha20Poly1305.sealArm, Proof.ChaCha20Poly1305.preArm, Proof.ChaCha20Poly1305.pubArm, Arm.abi,
      Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
      [Proof.ChaCha20Poly1305.Arm.sat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read]
      using Proof.ChaCha20Poly1305.Arm.sat)

/-- The postconditions match on `decrypt`; the result is the low word of
`r1:r0`. -/
theorem «open» :
    Verified Arm.target Impl.ChaCha20Poly1305.Arm.«open» (Spec.ChaCha20Poly1305.openContract Arm.abi 8) :=
  Proof.ChaCha20Poly1305.Arm.open_verified.of_implies
    { pre := by
        implies_pre [Spec.ChaCha20Poly1305.openContract, Spec.ChaCha20Poly1305.openSig,
          Proof.ChaCha20Poly1305.openArm, Proof.ChaCha20Poly1305.preArm, Proof.ChaCha20Poly1305.pubArm, Arm.abi,
          Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
      post := by
        intro s s' _ h
        sig_unfold [Spec.ChaCha20Poly1305.openContract, Spec.ChaCha20Poly1305.openSig, Arm.abi, Arm.argRegs,
          Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
        simp only [Proof.ChaCha20Poly1305.openArm, Arm.State.addr] at h
        have e : ∀ x y : BitVec 32, (x ++ y).setWidth 32 = y := fun _ _ => BitVec.setWidth_append_eq_right
        split at h
        next _ pt e₁ =>
          split
          next _ pt' e₂ =>
            obtain rfl := Option.some.inj (e₁.symm.trans e₂)
            exact ⟨(e _ _).trans h.1, h.2⟩
          next _ e₂ => exact absurd (e₁.symm.trans e₂) (by simp)
        next _ e₁ =>
          split
          next _ pt' e₂ => exact absurd (e₁.symm.trans e₂) (by simp)
          next _ e₂ => exact (e _ _).trans h
      pub := by
        implies_pub [Spec.ChaCha20Poly1305.openContract, Spec.ChaCha20Poly1305.openSig,
          Proof.ChaCha20Poly1305.openArm, Proof.ChaCha20Poly1305.preArm, Proof.ChaCha20Poly1305.pubArm, Arm.abi,
          Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
      sat := by
        implies_sat [Spec.ChaCha20Poly1305.openContract, Spec.ChaCha20Poly1305.openSig,
          Proof.ChaCha20Poly1305.openArm, Proof.ChaCha20Poly1305.preArm, Proof.ChaCha20Poly1305.pubArm, Arm.abi,
          Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr, Proof.ChaCha20Poly1305.Arm.sat,
          Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read] using Proof.ChaCha20Poly1305.Arm.sat }

end VG.Proof.ChaCha20Poly1305.Arm.Shared
