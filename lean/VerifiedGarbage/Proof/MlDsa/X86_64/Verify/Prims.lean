import VerifiedGarbage.Proof.MlDsa.X86_64.Verify.Verified
import VerifiedGarbage.Proof.MlKem.X86_64.FragPrim
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.AddSub
import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.Mul
import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.NttInv
import VerifiedGarbage.Proof.MlDsa.X86_64.Sample.RejNttCT
import VerifiedGarbage.Proof.MlDsa.X86_64.Sample.BallCT
import VerifiedGarbage.Proof.MlDsa.X86_64.Round.NormLt
import VerifiedGarbage.Proof.MlDsa.X86_64.Round.UseHint
import VerifiedGarbage.Proof.MlDsa.X86_64.Pack.SimpleBitPack
import VerifiedGarbage.Proof.MlDsa.X86_64.Pack.Unpack
import VerifiedGarbage.Proof.MlDsa.X86_64.Pack.HintUnpack

/-!
# ML-DSA verification on x86-64: the primitives it calls

Untrusted: everything here is checked by Lean. The x86-64 implementations
of the primitives (`prims`) meet their contracts with at most 16 bytes of
stack, never write the stack pointer or load MXCSR, and call at most two
deep (`prims_ok`), so `verify prims p` meets `verifyContract p`.
-/

namespace VG.Proof.MlDsa.X86_64.Verify

open VG VG.X86_64 VG.Impl.MlDsa.X86_64.Verify
open VG.Impl.MlDsa.X86_64

/-- The x86-64 implementations of the primitives. -/
def prims : Prims where
  ntt := Arith.ntt
  invNtt := Arith.nttInv
  mul := Arith.mul
  mulAdd := Arith.mulAdd
  sub := Arith.sub
  rejNtt := Sample.rejNTT
  ball := Sample.sampleInBall
  useHint := Round.useHint
  simpleBitPack := Pack.simpleBitPack
  bitUnpack := Pack.bitUnpack
  unpackT1 := Pack.unpackT1
  hintUnpack := Pack.hintBitUnpack
  normLt := Round.normLt

theorem prims_ok : PrimsOk prims where
  ntt := by
    have h := Proof.MlDsa.X86_64.Arith.ntt_verified
    unfold Spec.MlDsa.nttContract Spec.MlDsa.inPlaceContract at h ⊢
    exact CalleeOk.of_verified h (by decide) (Proof.MlKem.X86_64.nosp_of (by lit_decide)) (by lit_decide)
      (by lit_decide) (Code.all_of_allInstrs (by lit_decide))
  invNtt := by
    have h := Proof.MlDsa.X86_64.Arith.nttInv_verified
    unfold Spec.MlDsa.nttInvContract Spec.MlDsa.inPlaceContract at h ⊢
    exact CalleeOk.of_verified h (by decide) (Proof.MlKem.X86_64.nosp_of (by lit_decide)) (by lit_decide)
      (by lit_decide) (Code.all_of_allInstrs (by lit_decide))
  mul := CalleeOk.of_verified Proof.MlDsa.X86_64.Arith.mul_verified (by decide)
    (Proof.MlKem.X86_64.nosp_of (by lit_decide)) (by lit_decide) (by lit_decide)
    (Code.all_of_allInstrs (by lit_decide))
  mulAdd := CalleeOk.of_verified Proof.MlDsa.X86_64.Arith.mulAdd_verified (by decide)
    (Proof.MlKem.X86_64.nosp_of (by lit_decide)) (by lit_decide) (by lit_decide)
    (Code.all_of_allInstrs (by lit_decide))
  sub := CalleeOk.of_verified Proof.MlDsa.X86_64.Arith.sub_verified (by decide)
    (Proof.MlKem.X86_64.nosp_of (by lit_decide)) (by lit_decide) (by lit_decide)
    (Code.all_of_allInstrs (by lit_decide))
  rejNtt := CalleeOk.of_verified Proof.MlDsa.X86_64.Sample.rejNTT_verified (by decide)
    (Proof.MlKem.X86_64.nosp_of (by lit_decide)) (by lit_decide) (by lit_decide)
    (Code.all_of_allInstrs (by lit_decide))
  ball := CalleeOk.of_verified Proof.MlDsa.X86_64.Sample.sampleInBall_verified (by decide)
    (Proof.MlKem.X86_64.nosp_of (by lit_decide)) (by lit_decide) (by lit_decide)
    (Code.all_of_allInstrs (by lit_decide))
  useHint := CalleeOk.of_verified Proof.MlDsa.X86_64.Round.useHint_verified (by decide)
    (Proof.MlKem.X86_64.nosp_of (by lit_decide)) (by lit_decide) (by lit_decide)
    (Code.all_of_allInstrs (by lit_decide))
  simpleBitPack := CalleeOk.of_verified Proof.MlDsa.X86_64.Pack.simpleBitPack_verified (by decide)
    (Proof.MlKem.X86_64.nosp_of (by lit_decide)) (by lit_decide) (by lit_decide)
    (Code.all_of_allInstrs (by lit_decide))
  bitUnpack := CalleeOk.of_verified Proof.MlDsa.X86_64.Pack.bitUnpack_verified (by decide)
    (Proof.MlKem.X86_64.nosp_of (by lit_decide)) (by lit_decide) (by lit_decide)
    (Code.all_of_allInstrs (by lit_decide))
  unpackT1 := CalleeOk.of_verified Proof.MlDsa.X86_64.Pack.unpackT1_verified (by decide)
    (Proof.MlKem.X86_64.nosp_of (by lit_decide)) (by lit_decide) (by lit_decide)
    (Code.all_of_allInstrs (by lit_decide))
  hintUnpack := CalleeOk.of_verified Proof.MlDsa.X86_64.Pack.hintBitUnpack_verified (by decide)
    (Proof.MlKem.X86_64.nosp_of (by lit_decide)) (by lit_decide) (by lit_decide)
    (Code.all_of_allInstrs (by lit_decide))
  normLt := CalleeOk.of_verified Proof.MlDsa.X86_64.Round.normLt_verified (by decide)
    (Proof.MlKem.X86_64.nosp_of (by lit_decide)) (by lit_decide) (by lit_decide)
    (Code.all_of_allInstrs (by lit_decide))

/-- `vg_mldsa*_verify` for the parameter set `p`, calling the x86-64 primitives. -/
theorem verify_prims {p : Spec.MlDsa.Params} (hp : p ∈ params) :
    Verified X86_64.target (verify prims p) (Spec.MlDsa.verifyContract p X86_64.abi 24) :=
  verify_verified prims_ok hp

end VG.Proof.MlDsa.X86_64.Verify
