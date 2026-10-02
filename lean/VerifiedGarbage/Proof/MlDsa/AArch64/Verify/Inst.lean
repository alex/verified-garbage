import VerifiedGarbage.Proof.MlDsa.AArch64.Verify.Final
import VerifiedGarbage.Proof.MlDsa.AArch64.KeyGen.Inst

/-!
# ML-DSA verification on AArch64, with this library's primitives

Verification with the AArch64 implementations of the primitives (`prims_ok`)
is verified with 16 bytes of stack (`verify44_verified`, …).
-/

namespace VG.Proof.MlDsa.AArch64.Verify

variable {keccak : VG.Proof.Sha3.AArch64.Permutation}

open VG VG.AArch64 VG.Impl.MlDsa.AArch64.Call VG.Impl.MlDsa.AArch64.KeyGen
open VG.Proof.MlDsa.AArch64.KeyGen (prims_okWith scrLen)

/-- A state satisfying `verifyContract`'s precondition. -/
def vSat (p : Spec.MlDsa.Params) : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 0x10000 | .x2 => 0x20000 | .x3 => 0x100000 | _ => 0
  sp := 0x1000000
  mem _ := 0
  rd := [⟨0x1000, p.pkLen⟩, ⟨0x10000, 64⟩, ⟨0x20000, p.sigLen⟩]
  wr := [⟨0x100000, scrLen p⟩]

theorem verify_sat (p : Spec.MlDsa.Params)
    (hp : p = Spec.MlDsa.mlDsa44 ∨ p = Spec.MlDsa.mlDsa65 ∨ p = Spec.MlDsa.mlDsa87) :
    ∃ s, (Spec.MlDsa.verifyContract p AArch64.abi 16).pre s := by
  rcases hp with rfl | rfl | rfl
  · refine ⟨vSat Spec.MlDsa.mlDsa44, ?_⟩
    sig_sat_check [Spec.MlDsa.verifyContract, Spec.MlDsa.verifySig, AArch64.abi, VG.AArch64.argRegs]
  · refine ⟨vSat Spec.MlDsa.mlDsa65, ?_⟩
    sig_sat_check [Spec.MlDsa.verifyContract, Spec.MlDsa.verifySig, AArch64.abi, VG.AArch64.argRegs]
  · refine ⟨vSat Spec.MlDsa.mlDsa87, ?_⟩
    sig_sat_check [Spec.MlDsa.verifyContract, Spec.MlDsa.verifySig, AArch64.abi, VG.AArch64.argRegs]

theorem verify44_verifiedWith :
    Verified AArch64.target (verify44With keccak.callee) (Spec.MlDsa.verifyContract Spec.MlDsa.mlDsa44 AArch64.abi 16) :=
  verify_verified (keccak := keccak) (prims_okWith (keccak := keccak)) Spec.MlDsa.mlDsa44 (.inl rfl) (verify_sat _ (.inl rfl))

theorem verify65_verifiedWith :
    Verified AArch64.target (verify65With keccak.callee) (Spec.MlDsa.verifyContract Spec.MlDsa.mlDsa65 AArch64.abi 16) :=
  verify_verified (keccak := keccak) (prims_okWith (keccak := keccak)) Spec.MlDsa.mlDsa65 (.inr (.inl rfl)) (verify_sat _ (.inr (.inl rfl)))

theorem verify87_verifiedWith :
    Verified AArch64.target (verify87With keccak.callee) (Spec.MlDsa.verifyContract Spec.MlDsa.mlDsa87 AArch64.abi 16) :=
  verify_verified (keccak := keccak) (prims_okWith (keccak := keccak)) Spec.MlDsa.mlDsa87 (.inr (.inr rfl)) (verify_sat _ (.inr (.inr rfl)))

theorem verify44_verified :
    Verified AArch64.target verify44 (Spec.MlDsa.verifyContract Spec.MlDsa.mlDsa44 AArch64.abi 16) :=
  verify44_verifiedWith (keccak := .scalar)

theorem verify65_verified :
    Verified AArch64.target verify65 (Spec.MlDsa.verifyContract Spec.MlDsa.mlDsa65 AArch64.abi 16) :=
  verify65_verifiedWith (keccak := .scalar)

theorem verify87_verified :
    Verified AArch64.target verify87 (Spec.MlDsa.verifyContract Spec.MlDsa.mlDsa87 AArch64.abi 16) :=
  verify87_verifiedWith (keccak := .scalar)

end VG.Proof.MlDsa.AArch64.Verify
