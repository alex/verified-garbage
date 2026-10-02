import VerifiedGarbage.Proof.MlDsa.X86_64.Verify.Control

/-!
# ML-DSA verification on x86-64: what the proofs need of the primitives

Untrusted: everything here is checked by Lean. `PrimsOk P`: each primitive
of `P` is correct and constant time under its shared contract with at most
16 bytes of stack (`CalleeOk`, from its `Verified` proof by
`CalleeOk.of_verified`; 24 for `vg_mldsa_rej_ntt_poly4`), never writes the
stack pointer, calls at most three deep and never loads MXCSR. The proofs
of `vg_mldsa*_verify` hold for any such `P`.
-/

namespace VG.Proof.MlDsa.X86_64.Verify

open VG VG.X86_64 VG.Impl.MlDsa.X86_64.Verify
open VG.Spec.MlDsa

/-- Implementations of the primitives, correct and constant time. -/
structure PrimsOk (P : Prims) : Prop where
  ntt : CalleeOk P.ntt (nttContract X86_64.abi 16)
  invNtt : CalleeOk P.invNtt (nttInvContract X86_64.abi 16)
  mul : CalleeOk P.mul (mulContract X86_64.abi 16)
  mulAdd : CalleeOk P.mulAdd (mulAddContract X86_64.abi 16)
  sub : CalleeOk P.sub (subContract X86_64.abi 16)
  rejNtt : CalleeOk P.rejNtt (rejNTTContract X86_64.abi 16)
  ball : CalleeOk P.ball (sampleInBallContract X86_64.abi 16)
  useHint : CalleeOk P.useHint (useHintContract X86_64.abi 16)
  simpleBitPack : CalleeOk P.simpleBitPack (simpleBitPackContract X86_64.abi 16)
  bitUnpack : CalleeOk P.bitUnpack (bitUnpackContract X86_64.abi 16)
  unpackT1 : CalleeOk P.unpackT1 (unpackT1Contract X86_64.abi 16)
  hintUnpack : CalleeOk P.hintUnpack (hintBitUnpackContract X86_64.abi 16)
  normLt : CalleeOk P.normLt (normLtContract X86_64.abi 16)
  rej4 : CalleeOk P.rej4 (rejNTT4Contract X86_64.abi 24)

end VG.Proof.MlDsa.X86_64.Verify
