import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Pbkdf2.Arm.Iterate
import VerifiedGarbage.Spec.Pbkdf2.Contract

/-!
# PBKDF2-HMAC-SHA-256 on ARMv7: the shared contract

Untrusted: everything here is checked by Lean. The proof is written against
a per-target contract (`Proof/Pbkdf2/Arm/Contract.lean`); this theorem moves
it to the shared contract of `Spec/Pbkdf2/Contract.lean`, which the artifact
is emitted with. The function uses no stack: `bl` leaves the return address
in `lr`, which it saves in `scratch`.
-/

namespace VG.Proof.Pbkdf2.Arm.Shared

theorem iterate :
    Verified Arm.target Impl.Pbkdf2.Arm.iterate (Spec.Pbkdf2.iterateSha256Contract Arm.abi) :=
  Proof.Pbkdf2.Arm.iterate_verified.of_implies (by
    contract_implies [Spec.Pbkdf2.iterateSha256Contract, Spec.Pbkdf2.iterateSha256Sig,
      Proof.Pbkdf2.iterateSha256Arm, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
      [Proof.Pbkdf2.Arm.sat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read] using Proof.Pbkdf2.Arm.sat)

end VG.Proof.Pbkdf2.Arm.Shared
