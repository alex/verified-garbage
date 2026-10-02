import VerifiedGarbage.Proof.MlKem.AArch64.Decaps
import VerifiedGarbage.Proof.MlKem1024.AArch64.Encaps
import VerifiedGarbage.Impl.MlKem1024.AArch64.Decaps

/-!
# ML-KEM-1024 on AArch64: `vg_mlkem1024_decaps`

ML-KEM-768's proof (`Proof/MlKem/AArch64/Kem*.lean`, `Decaps*.lean`), which is
stated for any well-formed parameter set, for ML-KEM-1024's (`lay1024`); the
taint analyses of its code are decided on its literals.
-/

namespace VG.Proof.MlKem1024.AArch64.Decaps

variable {keccak : VG.Proof.Sha3.AArch64.Permutation}

open VG VG.AArch64 VG.Impl.MlKem1024.AArch64 VG.Proof.MlKem VG.Proof.MlKem.AArch64
open VG.Proof.MlKem.AArch64.Kem VG.Proof.MlKem.AArch64.Decaps
open VG.Impl.MlKem.AArch64 (KemLay)

theorem taints1024 : DeTaints lay1024 keccak :=
  ⟨keccak.mlkem1024DeATaint, keccak.mlkem1024DeCTaint, Encaps.setupTaint1024⟩

/-- A state satisfying the precondition. -/
def sat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 0x2000 | .x2 => 0x3000 | .x3 => 0x10000 | _ => 0
  sp := 0x100000
  mem _ := 0
  rd := [⟨0x1000, 3168⟩, ⟨0x2000, 1568⟩]
  wr := [⟨0x3000, 32⟩, ⟨0x10000, 49152⟩]

theorem decaps_correctWith (s : State) (hs : (decapsAArch64 lay1024).pre s) :
    ∃ t s', Exec isa (decapsWith keccak.callee) s t s' ∧ abiPreserved s s' ∧
      (decapsAArch64 lay1024).post s s' :=
  decaps_correct KeyGen.wf1024 Encaps.calls1024 hs

theorem decaps_verifiedWith :
    Verified AArch64.target (decapsWith keccak.callee) (Spec.MlKem1024.decapsContract AArch64.abi 16) :=
  Verified.of_correct (decaps_correctWith (keccak := keccak))
    (ct KeyGen.wf1024 Encaps.calls1024 taints1024) (by
    mlkem_implies [Spec.MlKem1024.decapsContract, Spec.MlKem1024.decapsSig, decapsAArch64, lay1024,
      KemLay.params, Spec.MlKem.mlKem1024, KemLay.dkLen, KemLay.ctLen, AArch64.abi, AArch64.argRegs] [sat]
      using sat)

theorem decaps_verified :
    Verified AArch64.target decaps (Spec.MlKem1024.decapsContract AArch64.abi 16) :=
  decaps_verifiedWith (keccak := .scalar)

end VG.Proof.MlKem1024.AArch64.Decaps
