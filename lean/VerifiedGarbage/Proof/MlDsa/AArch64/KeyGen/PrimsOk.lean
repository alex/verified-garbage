import VerifiedGarbage.Proof.MlDsa.AArch64.KeyGen.Top

/-!
# ML-DSA on AArch64: what the proofs need of the primitives

`PrimsOk P S`: each primitive of `P` is correct and constant time under its
shared contract with `S` bytes of stack, and its frames use at most those `S`
bytes (`CalleeOk`, from its `Verified` proof by `CalleeOk.of_verified`); `S`
is at least the 16 bytes the sponge functions' frames use. The proofs of
`vg_mldsa*_keygen` and `vg_mldsa*_verify` hold for any such `P`, with their
contracts' stack `S`.
-/

namespace VG.Proof.MlDsa.AArch64.KeyGen

open VG VG.AArch64 VG.Impl.MlDsa.AArch64.KeyGen
open VG.Spec.MlDsa

/-- Implementations of the primitives, correct and constant time with `S`
bytes of stack. -/
structure PrimsOk (P : Prims) (S : Nat) : Prop where
  s16 : 16 ≤ S
  sl : S < 2 ^ 16
  ntt : CalleeOk S P.ntt (nttContract AArch64.abi S)
  invNtt : CalleeOk S P.invNtt (nttInvContract AArch64.abi S)
  mul : CalleeOk S P.mul (mulContract AArch64.abi S)
  mulAdd : CalleeOk S P.mulAdd (mulAddContract AArch64.abi S)
  add : CalleeOk S P.add (addContract AArch64.abi S)
  sub : CalleeOk S P.sub (subContract AArch64.abi S)
  rejNtt : CalleeOk S P.rejNtt (rejNTTContract AArch64.abi S)
  rejBounded : CalleeOk S P.rejBounded (rejBoundedContract AArch64.abi S)
  ball : CalleeOk S P.ball (sampleInBallContract AArch64.abi S)
  power2Round : CalleeOk S P.power2Round (power2RoundContract AArch64.abi S)
  useHint : CalleeOk S P.useHint (useHintContract AArch64.abi S)
  normLt : CalleeOk S P.normLt (normLtContract AArch64.abi S)
  simpleBitPack : CalleeOk S P.simpleBitPack (simpleBitPackContract AArch64.abi S)
  bitPack : CalleeOk S P.bitPack (bitPackContract AArch64.abi S)
  bitUnpack : CalleeOk S P.bitUnpack (bitUnpackContract AArch64.abi S)
  unpackT1 : CalleeOk S P.unpackT1 (unpackT1Contract AArch64.abi S)
  hintUnpack : CalleeOk S P.hintUnpack (hintBitUnpackContract AArch64.abi S)

theorem PrimsOk.s64 {P : Prims} {S : Nat} (h : PrimsOk P S) : S < 2 ^ 64 := by have := h.sl; omega

end VG.Proof.MlDsa.AArch64.KeyGen
