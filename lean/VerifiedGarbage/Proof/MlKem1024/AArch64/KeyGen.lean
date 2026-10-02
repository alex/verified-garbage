import VerifiedGarbage.Proof.MlKem.AArch64.KeyGen
import VerifiedGarbage.Impl.MlKem1024.AArch64.KeyGen
import VerifiedGarbage.Spec.MlKem.Contract1024

/-!
# ML-KEM-1024 on AArch64: `vg_mlkem1024_keygen`

ML-KEM-768's proof (`Proof/MlKem/AArch64/Kg*.lean`, `KeyGen.lean`), which is
stated for any well-formed parameter set, for ML-KEM-1024's (`lay1024`):
that it is well formed, and the taint analyses of its code, are decided on
its literals.
-/

namespace VG.Proof.MlKem1024.AArch64.KeyGen

variable {keccak : VG.Proof.Sha3.AArch64.Permutation}

open VG VG.AArch64 VG.Impl.MlKem1024.AArch64 VG.Proof.MlKem VG.Proof.MlKem.AArch64 VG.Proof.MlKem.AArch64.KeyGen
open VG.Impl.MlKem.AArch64 (KemLay)

theorem wf1024 : lay1024.Wf := ⟨by decide⟩

theorem taints1024 : KgTaints lay1024 keccak :=
  ⟨keccak.mlkem1024KgATaint, keccak.mlkem1024KgCTaint, by
    intro i hi j hj
    change i < 4 at hi
    change j < 4 at hj
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with rfl | rfl | rfl | rfl <;>
    rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3) with rfl | rfl | rfl | rfl <;>
    exact ⟨_, by taint_decide⟩⟩

/-- A state satisfying the precondition. -/
def sat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 0x2000 | .x2 => 0x3000 | .x3 => 0x10000 | _ => 0
  sp := 0x100000
  mem _ := 0
  rd := [⟨0x1000, 64⟩]
  wr := [⟨0x2000, 1568⟩, ⟨0x3000, 3168⟩, ⟨0x10000, 49152⟩]

theorem keyGen_correctWith (s : State) (hs : (keyGenAArch64 lay1024).pre s) :
    ∃ t s', Exec isa (keyGenWith keccak.callee) s t s' ∧ abiPreserved s s' ∧
      (keyGenAArch64 lay1024).post s s' :=
  keyGen_correct wf1024 hs

theorem keyGen_verifiedWith :
    Verified AArch64.target (keyGenWith keccak.callee) (Spec.MlKem1024.keyGenContract AArch64.abi 16) :=
  Verified.of_correct (keyGen_correctWith (keccak := keccak)) (ct wf1024 taints1024) (by
    mlkem_implies [Spec.MlKem1024.keyGenContract, Spec.MlKem1024.keyGenSig, keyGenAArch64, lay1024,
      KemLay.params, Spec.MlKem.mlKem1024, KemLay.ekLen, KemLay.dkLen, AArch64.abi, AArch64.argRegs] [sat]
      using sat)

theorem keyGen_verified :
    Verified AArch64.target keyGen (Spec.MlKem1024.keyGenContract AArch64.abi 16) :=
  keyGen_verifiedWith (keccak := .scalar)

end VG.Proof.MlKem1024.AArch64.KeyGen
