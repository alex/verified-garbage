import VerifiedGarbage.Proof.MlDsa.X86_64.KeyGen.Top
import VerifiedGarbage.Impl.MlDsa.X86_64.KeyGen.Inst
import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.Ntt
import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.NttInv
import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.Mul
import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.AddSub
import VerifiedGarbage.Proof.MlDsa.X86_64.Sample.RejNttCT
import VerifiedGarbage.Proof.MlDsa.X86_64.Sample.RejBoundedCT
import VerifiedGarbage.Proof.MlDsa.X86_64.Round.Power2Round
import VerifiedGarbage.Proof.MlDsa.X86_64.Pack.SimpleBitPack
import VerifiedGarbage.Proof.MlDsa.X86_64.Pack.BitPack

/-!
# ML-DSA key generation on x86-64, with this library's primitives

Untrusted: everything here is checked by Lean. The x86-64 implementations of
the primitives (`prims`) are verified, use at most 16 bytes of stack, and
never write `rsp` but by calls nested at most twice (`prims_ok`), so key
generation with them is verified (`keyGen44_verified`, …).
-/

namespace VG.Proof.MlDsa.X86_64.KeyGen

open VG VG.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.MlDsa.X86_64.KeyGen

theorem prims_ok : PrimsOk prims where
  ntt := ⟨⟨0, by decide, Arith.ntt_verified⟩, nosp_of (by decide +kernel), by decide +kernel⟩
  invNtt := ⟨⟨0, by decide, Arith.nttInv_verified⟩, nosp_of (by decide +kernel), by decide +kernel⟩
  mul := ⟨⟨0, by decide, Arith.mul_verified⟩, nosp_of (by decide +kernel), by decide +kernel⟩
  mulAdd := ⟨⟨0, by decide, Arith.mulAdd_verified⟩, nosp_of (by decide +kernel), by decide +kernel⟩
  add := ⟨⟨0, by decide, Arith.add_verified⟩, nosp_of (by decide +kernel), by decide +kernel⟩
  rejNtt := ⟨⟨16, by decide, Sample.rejNTT_verified⟩, nosp_of (by decide +kernel), by decide +kernel⟩
  rejBounded := ⟨⟨16, by decide, Sample.rejBounded_verified⟩, nosp_of (by decide +kernel), by decide +kernel⟩
  power2Round := ⟨⟨0, by decide, Round.power2Round_verified⟩, nosp_of (by decide +kernel), by decide +kernel⟩
  simpleBitPack := ⟨⟨0, by decide, Pack.simpleBitPack_verified⟩, nosp_of (by decide +kernel),
    by decide +kernel⟩
  bitPack := ⟨⟨0, by decide, Pack.bitPack_verified⟩, nosp_of (by decide +kernel), by decide +kernel⟩

theorem keyGen44_verified :
    Verified X86_64.target keyGen44 (Spec.MlDsa.keyGenContract Spec.MlDsa.mlDsa44 X86_64.abi 32) :=
  keyGen_verified prims_ok _ (.inl rfl)

theorem keyGen65_verified :
    Verified X86_64.target keyGen65 (Spec.MlDsa.keyGenContract Spec.MlDsa.mlDsa65 X86_64.abi 32) :=
  keyGen_verified prims_ok _ (.inr (.inl rfl))

theorem keyGen87_verified :
    Verified X86_64.target keyGen87 (Spec.MlDsa.keyGenContract Spec.MlDsa.mlDsa87 X86_64.abi 32) :=
  keyGen_verified prims_ok _ (.inr (.inr rfl))

end VG.Proof.MlDsa.X86_64.KeyGen
