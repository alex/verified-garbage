import VerifiedGarbage.Proof.MlDsa.X86.Verify.Verified
import VerifiedGarbage.Impl.MlDsa.X86.Verify.Inst
import VerifiedGarbage.Proof.MlDsa.X86.Arith.AddSub
import VerifiedGarbage.Proof.MlDsa.X86.Arith.Mul
import VerifiedGarbage.Proof.MlDsa.X86.Arith.Ntt
import VerifiedGarbage.Proof.MlDsa.X86.Arith.NttInv
import VerifiedGarbage.Proof.MlDsa.X86.Sample.RejNtt
import VerifiedGarbage.Proof.MlDsa.X86.Sample.BallTop
import VerifiedGarbage.Proof.MlDsa.X86.Round.NormLt
import VerifiedGarbage.Proof.MlDsa.X86.Round.HintF
import VerifiedGarbage.Proof.MlDsa.X86.Pack.SimpleBitPack
import VerifiedGarbage.Proof.MlDsa.X86.Pack.Unpack
import VerifiedGarbage.Proof.MlDsa.X86.Pack.HintUnpackEnd

/-!
# ML-DSA verification on x86 (32-bit), with this library's primitives

Untrusted: everything here is checked by Lean. The x86 primitives
(`Impl.MlDsa.X86.Verify.prims`) are verified against their contracts, use at
most 56 bytes of stack and write `esp` only by frames and calls
(`prims_ok`), so `vg_mldsa{44,65,87}_verify` meet theirs
(`verify44_verified`, …).
-/

namespace VG.Proof.MlDsa.X86.Verify

open VG VG.X86 VG.Proof.MlDsa.X86.KeyGen
open VG.Impl.MlDsa.X86.Verify (prims verify44 verify65 verify87)

theorem prims_ok : PrimsOk prims where
  ntt := ⟨⟨15, by decide, Arith.NttFwd.verified⟩, by decide +kernel, NoSp.of_all (by decide +kernel)⟩
  invNtt := ⟨⟨15, by decide, Arith.NttInvP.verified⟩, by decide +kernel, NoSp.of_all (by decide +kernel)⟩
  mul := ⟨⟨15, by decide, Arith.mul_verified⟩, by decide +kernel, NoSp.of_all (by decide +kernel)⟩
  mulAdd := ⟨⟨15, by decide, Arith.mulAdd_verified⟩, by decide +kernel, NoSp.of_all (by decide +kernel)⟩
  sub := ⟨⟨15, by decide, Arith.sub_verified⟩, by decide +kernel, NoSp.of_all (by decide +kernel)⟩
  rejNtt := ⟨⟨55, by decide, Sample.RejNtt.verified⟩, by decide +kernel, NoSp.of_all (by decide +kernel)⟩
  ball := ⟨⟨55, by decide, Sample.Ball.verified⟩, by decide +kernel, NoSp.of_all (by decide +kernel)⟩
  useHint := ⟨⟨15, by decide, Round.useHint_verified⟩, by decide +kernel, NoSp.of_all (by decide +kernel)⟩
  simpleBitPack := ⟨⟨15, by decide, Pack.SimpleBitPack.verified⟩, by decide +kernel,
    NoSp.of_all (by decide +kernel)⟩
  bitUnpack := ⟨⟨15, by decide, Pack.Unpack.BU.verified⟩, by decide +kernel, NoSp.of_all (by decide +kernel)⟩
  unpackT1 := ⟨⟨15, by decide, Pack.Unpack.T1.verified⟩, by decide +kernel, NoSp.of_all (by decide +kernel)⟩
  hintUnpack := ⟨⟨15, by decide, Pack.Hint.hintBitUnpack_verified⟩, by decide +kernel,
    NoSp.of_all (by decide +kernel)⟩
  normLt := ⟨⟨15, by decide, Round.normLt_verified⟩, by decide +kernel, NoSp.of_all (by decide +kernel)⟩

theorem verify44_verified :
    Verified X86.target verify44 (Spec.MlDsa.verifyContract Spec.MlDsa.mlDsa44 X86.abi 96) :=
  verify_verified prims_ok _ (.inl rfl)

theorem verify65_verified :
    Verified X86.target verify65 (Spec.MlDsa.verifyContract Spec.MlDsa.mlDsa65 X86.abi 96) :=
  verify_verified prims_ok _ (.inr (.inl rfl))

theorem verify87_verified :
    Verified X86.target verify87 (Spec.MlDsa.verifyContract Spec.MlDsa.mlDsa87 X86.abi 96) :=
  verify_verified prims_ok _ (.inr (.inr rfl))

end VG.Proof.MlDsa.X86.Verify
