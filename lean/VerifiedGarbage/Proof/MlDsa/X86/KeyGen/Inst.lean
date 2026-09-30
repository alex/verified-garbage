import VerifiedGarbage.Proof.MlDsa.X86.KeyGen.Verified
import VerifiedGarbage.Impl.MlDsa.X86.KeyGen.Inst
import VerifiedGarbage.Proof.MlDsa.X86.Arith.AddSub
import VerifiedGarbage.Proof.MlDsa.X86.Arith.Mul
import VerifiedGarbage.Proof.MlDsa.X86.Arith.Ntt
import VerifiedGarbage.Proof.MlDsa.X86.Arith.NttInv
import VerifiedGarbage.Proof.MlDsa.X86.Sample.RejNtt
import VerifiedGarbage.Proof.MlDsa.X86.Sample.RejBounded
import VerifiedGarbage.Proof.MlDsa.X86.Round.Power2Round
import VerifiedGarbage.Proof.MlDsa.X86.Pack.SimpleBitPack
import VerifiedGarbage.Proof.MlDsa.X86.Pack.BitPack

/-!
# ML-DSA key generation on x86 (32-bit), with this library's primitives

Untrusted: everything here is checked by Lean. The x86 primitives
(`Impl.MlDsa.X86.KeyGen.prims`) are verified against their contracts, use at
most 56 bytes of stack and write `esp` only by frames and calls
(`prims_ok`), so `vg_mldsa{44,65,87}_keygen` meet theirs
(`keyGen44_verified`, …).
-/

namespace VG.Proof.MlDsa.X86.KeyGen

open VG VG.X86
open VG.Impl.MlDsa.X86.KeyGen (prims keyGen44 keyGen65 keyGen87)

theorem prims_ok : PrimsOk prims where
  ntt := ⟨⟨15, by decide, Arith.NttFwd.verified⟩, by decide +kernel, NoSp.of_all (by decide +kernel)⟩
  invNtt := ⟨⟨15, by decide, Arith.NttInvP.verified⟩, by decide +kernel, NoSp.of_all (by decide +kernel)⟩
  mul := ⟨⟨15, by decide, Arith.mul_verified⟩, by decide +kernel, NoSp.of_all (by decide +kernel)⟩
  mulAdd := ⟨⟨15, by decide, Arith.mulAdd_verified⟩, by decide +kernel, NoSp.of_all (by decide +kernel)⟩
  add := ⟨⟨15, by decide, Arith.add_verified⟩, by decide +kernel, NoSp.of_all (by decide +kernel)⟩
  rejNtt := ⟨⟨55, by decide, Sample.RejNtt.verified⟩, by decide +kernel, NoSp.of_all (by decide +kernel)⟩
  rejBounded := ⟨⟨55, by decide, Sample.RejBounded.verified⟩, by decide +kernel, NoSp.of_all (by decide +kernel)⟩
  power2Round := ⟨⟨15, by decide, Round.power2Round_verified⟩, by decide +kernel, NoSp.of_all (by decide +kernel)⟩
  simpleBitPack := ⟨⟨15, by decide, Pack.SimpleBitPack.verified⟩, by decide +kernel,
    NoSp.of_all (by decide +kernel)⟩
  bitPack := ⟨⟨15, by decide, Pack.BitPack.verified⟩, by decide +kernel, NoSp.of_all (by decide +kernel)⟩

theorem keyGen44_verified :
    Verified X86.target keyGen44 (Spec.MlDsa.keyGenContract Spec.MlDsa.mlDsa44 X86.abi 96) :=
  keyGen_verified prims_ok _ (.inl rfl)

theorem keyGen65_verified :
    Verified X86.target keyGen65 (Spec.MlDsa.keyGenContract Spec.MlDsa.mlDsa65 X86.abi 96) :=
  keyGen_verified prims_ok _ (.inr (.inl rfl))

theorem keyGen87_verified :
    Verified X86.target keyGen87 (Spec.MlDsa.keyGenContract Spec.MlDsa.mlDsa87 X86.abi 96) :=
  keyGen_verified prims_ok _ (.inr (.inr rfl))

end VG.Proof.MlDsa.X86.KeyGen
