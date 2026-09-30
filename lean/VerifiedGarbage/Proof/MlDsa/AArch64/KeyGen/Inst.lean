import VerifiedGarbage.Proof.MlDsa.AArch64.KeyGen.Main
import VerifiedGarbage.Impl.MlDsa.AArch64.KeyGen.Prims
import VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Ntt
import VerifiedGarbage.Proof.MlDsa.AArch64.Arith.NttInv
import VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Mul
import VerifiedGarbage.Proof.MlDsa.AArch64.Arith.AddSub
import VerifiedGarbage.Proof.MlDsa.AArch64.Round.Power2Round
import VerifiedGarbage.Proof.MlDsa.AArch64.Round.UseHint
import VerifiedGarbage.Proof.MlDsa.AArch64.Round.NormLt
import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.RejNttCT
import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.RejBoundedCT
import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Ball
import VerifiedGarbage.Proof.MlDsa.AArch64.Pack.SimpleBitPack
import VerifiedGarbage.Proof.MlDsa.AArch64.Pack.BitPack
import VerifiedGarbage.Proof.MlDsa.AArch64.Pack.Unpack
import VerifiedGarbage.Proof.MlDsa.AArch64.Pack.HintUnpack

/-!
# ML-DSA key generation on AArch64, with this library's primitives

Untrusted: everything here is checked by Lean. The AArch64 implementations
of the primitives (`prims`) are verified with at most 16 bytes of stack, and
their frames use at most that (`prims_ok`), so key generation with them is
verified with 16 bytes of stack (`keyGen44_verified`, …).
-/

namespace VG.Proof.MlDsa.AArch64.KeyGen

open VG VG.AArch64 VG.Impl.MlDsa.AArch64.KeyGen

theorem prims_ok : PrimsOk prims 16 where
  s16 := Nat.le_refl _
  sl := by decide
  ntt := by
    have h := Arith.ntt_verified
    unfold Spec.MlDsa.nttContract Spec.MlDsa.inPlaceContract at h ⊢
    exact CalleeOk.of_verified (by decide) h (by decide) (by decide)
  invNtt := by
    have h := Arith.nttInv_verified
    unfold Spec.MlDsa.nttInvContract Spec.MlDsa.inPlaceContract at h ⊢
    exact CalleeOk.of_verified (by decide) h (by decide) (by decide)
  mul := CalleeOk.of_verified (by decide) Arith.mul_verified (by decide) (by decide)
  mulAdd := CalleeOk.of_verified (by decide) Arith.mulAdd_verified (by decide) (by decide)
  add := CalleeOk.of_verified (by decide) Arith.add_verified (by decide) (by decide)
  sub := CalleeOk.of_verified (by decide) Arith.sub_verified (by decide) (by decide)
  rejNtt := CalleeOk.of_verified (by decide) Sample.rejNTT_verified (by decide) (by decide)
  rejBounded := CalleeOk.of_verified (by decide) Sample.rejBounded_verified (by decide) (by decide)
  ball := CalleeOk.of_verified (by decide) Sample.sampleInBall_verified (by decide) (by decide)
  power2Round := CalleeOk.of_verified (by decide) Round.power2Round_verified (by decide) (by decide)
  useHint := CalleeOk.of_verified (by decide) Round.useHint_verified (by decide) (by decide)
  normLt := CalleeOk.of_verified (by decide) Round.normLt_verified (by decide) (by decide)
  simpleBitPack := CalleeOk.of_verified (by decide) Pack.simpleBitPack_verified (by decide) (by decide)
  bitPack := CalleeOk.of_verified (by decide) Pack.bitPack_verified (by decide) (by decide)
  bitUnpack := CalleeOk.of_verified (by decide) Pack.bitUnpack_verified (by decide) (by decide)
  unpackT1 := CalleeOk.of_verified (by decide) Pack.unpackT1_verified (by decide) (by decide)
  hintUnpack := CalleeOk.of_verified (by decide) Pack.hintBitUnpack_verified (by decide) (by decide)

/-- A state satisfying `keyGenContract`'s precondition. -/
def kgSat (p : Spec.MlDsa.Params) : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 0x10000 | .x2 => 0x20000 | .x3 => 0x100000 | _ => 0
  sp := 0x1000000
  mem _ := 0
  rd := [⟨0x1000, 32⟩]
  wr := [⟨0x10000, p.pkLen⟩, ⟨0x20000, p.skLen⟩, ⟨0x100000, scrLen p⟩]

theorem keyGen_sat (p : Spec.MlDsa.Params)
    (hp : p = Spec.MlDsa.mlDsa44 ∨ p = Spec.MlDsa.mlDsa65 ∨ p = Spec.MlDsa.mlDsa87) :
    ∃ s, (Spec.MlDsa.keyGenContract p AArch64.abi 16).pre s := by
  rcases hp with rfl | rfl | rfl
  · refine ⟨kgSat Spec.MlDsa.mlDsa44, ?_⟩
    sig_sat_check [Spec.MlDsa.keyGenContract, Spec.MlDsa.keyGenSig, AArch64.abi, VG.AArch64.argRegs]
  · refine ⟨kgSat Spec.MlDsa.mlDsa65, ?_⟩
    sig_sat_check [Spec.MlDsa.keyGenContract, Spec.MlDsa.keyGenSig, AArch64.abi, VG.AArch64.argRegs]
  · refine ⟨kgSat Spec.MlDsa.mlDsa87, ?_⟩
    sig_sat_check [Spec.MlDsa.keyGenContract, Spec.MlDsa.keyGenSig, AArch64.abi, VG.AArch64.argRegs]

theorem keyGen44_verified :
    Verified AArch64.target keyGen44 (Spec.MlDsa.keyGenContract Spec.MlDsa.mlDsa44 AArch64.abi 16) :=
  keyGen_verified prims_ok Spec.MlDsa.mlDsa44 (.inl rfl) (keyGen_sat _ (.inl rfl))

theorem keyGen65_verified :
    Verified AArch64.target keyGen65 (Spec.MlDsa.keyGenContract Spec.MlDsa.mlDsa65 AArch64.abi 16) :=
  keyGen_verified prims_ok Spec.MlDsa.mlDsa65 (.inr (.inl rfl)) (keyGen_sat _ (.inr (.inl rfl)))

theorem keyGen87_verified :
    Verified AArch64.target keyGen87 (Spec.MlDsa.keyGenContract Spec.MlDsa.mlDsa87 AArch64.abi 16) :=
  keyGen_verified prims_ok Spec.MlDsa.mlDsa87 (.inr (.inr rfl)) (keyGen_sat _ (.inr (.inr rfl)))

end VG.Proof.MlDsa.AArch64.KeyGen
