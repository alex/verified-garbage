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
import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.Backend

/-!
# ML-DSA verification on x86-64: the primitives it calls

The x86-64 implementations of the primitives (`prims`) meet their contracts
with at most 16 bytes of stack, never write the stack pointer or load MXCSR,
and call at most two deep, with any implementation `v` of the polynomial
arithmetic (`prims_okWith`), so `verify (primsWith v.code) p` meets
`verifyContract p`.
-/

namespace VG.Proof.MlDsa.X86_64.Verify

open VG VG.X86_64 VG.Impl.MlDsa.X86_64.Verify
open VG.Impl.MlDsa.X86_64
open VG.Proof.MlDsa.X86_64 (FnOk ArithImpl)

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
  rej4 := Sample.Rej4.rejNTT4

/-- The primitives, with the polynomial arithmetic of `B`. -/
def primsWith (B : Arith.Backend) : Prims :=
  { prims with
    ntt := B.ntt
    invNtt := B.invNtt
    mul := B.mul
    mulAdd := B.mulAdd
    sub := B.sub
    normLt := B.normLt
    rej4 := B.rej4
    sfx := B.sfx }

/-- A function of the polynomial arithmetic satisfies what the proofs of verification need of it. -/
theorem calleeOf {sig : Sig} {pre : Curry (sig.words X86_64.abi.ptrBits) (Mem → Prop)}
    {post : sig.Post X86_64.abi.ptrBits} {wa : Bool} {c : Prog isa}
    (h : FnOk (fun S => sig.contract X86_64.abi pre post wa S none) c) :
    CalleeOk c (sig.contract X86_64.abi pre post wa 16 none) :=
  CalleeOk.of_verified h.ver (by decide) h.nosp (Nat.le_succ_of_le h.depth) h.ctl h.sp

theorem prims_okWith (v : ArithImpl) : PrimsOk (primsWith v.code) where
  ntt := by
    have h := v.ok.ntt
    unfold Spec.MlDsa.nttContract Spec.MlDsa.inPlaceContract at h ⊢
    exact calleeOf h
  invNtt := by
    have h := v.ok.invNtt
    unfold Spec.MlDsa.nttInvContract Spec.MlDsa.inPlaceContract at h ⊢
    exact calleeOf h
  mul := calleeOf v.ok.mul
  mulAdd := calleeOf v.ok.mulAdd
  sub := calleeOf v.ok.sub
  rejNtt := (CalleeOk.of_verified Proof.MlDsa.X86_64.Sample.rejNTT_verified (by decide)
    (Proof.MlKem.X86_64.nosp_of (by lit_decide)) (by lit_decide) (by lit_decide)
    (Code.all_of_allInstrs (by lit_decide)) :
    CalleeOk prims.rejNtt _)
  ball := (CalleeOk.of_verified Proof.MlDsa.X86_64.Sample.sampleInBall_verified (by decide)
    (Proof.MlKem.X86_64.nosp_of (by lit_decide)) (by lit_decide) (by lit_decide)
    (Code.all_of_allInstrs (by lit_decide)) :
    CalleeOk prims.ball _)
  useHint := (CalleeOk.of_verified Proof.MlDsa.X86_64.Round.useHint_verified (by decide)
    (Proof.MlKem.X86_64.nosp_of (by lit_decide)) (by lit_decide) (by lit_decide)
    (Code.all_of_allInstrs (by lit_decide)) :
    CalleeOk prims.useHint _)
  simpleBitPack := (CalleeOk.of_verified Proof.MlDsa.X86_64.Pack.simpleBitPack_verified (by decide)
    (Proof.MlKem.X86_64.nosp_of (by lit_decide)) (by lit_decide) (by lit_decide)
    (Code.all_of_allInstrs (by lit_decide)) :
    CalleeOk prims.simpleBitPack _)
  bitUnpack := (CalleeOk.of_verified Proof.MlDsa.X86_64.Pack.bitUnpack_verified (by decide)
    (Proof.MlKem.X86_64.nosp_of (by lit_decide)) (by lit_decide) (by lit_decide)
    (Code.all_of_allInstrs (by lit_decide)) :
    CalleeOk prims.bitUnpack _)
  unpackT1 := (CalleeOk.of_verified Proof.MlDsa.X86_64.Pack.unpackT1_verified (by decide)
    (Proof.MlKem.X86_64.nosp_of (by lit_decide)) (by lit_decide) (by lit_decide)
    (Code.all_of_allInstrs (by lit_decide)) :
    CalleeOk prims.unpackT1 _)
  hintUnpack := (CalleeOk.of_verified Proof.MlDsa.X86_64.Pack.hintBitUnpack_verified (by decide)
    (Proof.MlKem.X86_64.nosp_of (by lit_decide)) (by lit_decide) (by lit_decide)
    (Code.all_of_allInstrs (by lit_decide)) :
    CalleeOk prims.hintUnpack _)
  normLt := calleeOf v.ok.normLt
  rej4 := ⟨v.ok.rej4.ver.1, v.ok.rej4.ver.2.1, v.ok.rej4.nosp, v.ok.rej4.depth, v.ok.rej4.ctl, v.ok.rej4.sp⟩

/-- `vg_mldsa*_verify` for the parameter set `p`, calling the x86-64
primitives, with the polynomial arithmetic of `v`. -/
theorem verify_prims (v : ArithImpl) {p : Spec.MlDsa.Params} (hp : p ∈ params) :
    Verified X86_64.target (verify (primsWith v.code) p) (Spec.MlDsa.verifyContract p X86_64.abi 32) :=
  verify_verified (prims_okWith v) hp

end VG.Proof.MlDsa.X86_64.Verify
