import VerifiedGarbage.Proof.MlKem.AArch64.Encaps
import VerifiedGarbage.Proof.MlKem1024.AArch64.KeyGen
import VerifiedGarbage.Proof.MlKem1024.AArch64.Args
import VerifiedGarbage.Impl.MlKem1024.AArch64.Encaps
import VerifiedGarbage.Spec.MlKem.Contract1024

/-!
# ML-KEM-1024 on AArch64: `vg_mlkem1024_encaps`

ML-KEM-768's proof (`Proof/MlKem/AArch64/Kem*.lean`, `Encaps.lean`), which is
stated for any well-formed parameter set, for ML-KEM-1024's (`lay1024`),
whose compression functions at the widths 11 and 5 are ML-KEM-1024's own
(`calls1024`); the taint analyses of its code are decided on its literals.
-/

namespace VG.Proof.MlKem1024.AArch64.Encaps

variable {keccak : VG.Proof.Sha3.AArch64.Permutation}

open VG VG.AArch64 VG.Impl.MlKem1024.AArch64 VG.Proof.MlKem VG.Proof.MlKem.AArch64
open VG.Proof.MlKem.AArch64.Kem VG.Proof.MlKem.AArch64.Encaps
open VG.Proof.MlKem1024.AArch64 (compressEncode1024_call decodeDecompress1024_call)
open VG.Impl.MlKem.AArch64 (KemLay)

theorem calls1024 : Calls lay1024 :=
  ⟨fun h0 h1 h2 h3 hd => compressEncode1024_call h0 h1 h2 h3 (by rcases hd with rfl | rfl <;> decide),
    fun h0 h1 h2 h3 hd => decodeDecompress1024_call h0 h1 h2 h3 (by rcases hd with rfl | rfl <;> decide)⟩

theorem setupTaint1024 : SetupTaint lay1024 := by
  intro i hi j hj
  change i < 4 at hi
  change j < 4 at hj
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with rfl | rfl | rfl | rfl <;>
  rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3) with rfl | rfl | rfl | rfl <;>
  exact ⟨_, by taint_decide⟩

theorem taints1024 : EnTaints lay1024 keccak :=
  ⟨keccak.mlkem1024EnATaint, keccak.mlkem1024EnCTaint, setupTaint1024⟩

/-- A state satisfying the precondition. -/
def sat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 0x2000 | .x2 => 0x3000 | .x3 => 0x4000 | .x4 => 0x10000 | _ => 0
  sp := 0x100000
  mem _ := 0
  rd := [⟨0x1000, 1568⟩, ⟨0x2000, 32⟩]
  wr := [⟨0x3000, 32⟩, ⟨0x4000, 1568⟩, ⟨0x10000, 49152⟩]

theorem encaps_correctWith (s : State) (hs : (encapsAArch64 lay1024).pre s) :
    ∃ t s', Exec isa (encapsWith keccak.callee) s t s' ∧ abiPreserved s s' ∧
      (encapsAArch64 lay1024).post s s' :=
  encaps_correct KeyGen.wf1024 calls1024 hs

theorem encaps_verifiedWith :
    Verified AArch64.target (encapsWith keccak.callee) (Spec.MlKem1024.encapsContract AArch64.abi 16) :=
  Verified.of_correct (encaps_correctWith (keccak := keccak)) (ct KeyGen.wf1024 taints1024) (by
    mlkem_implies [Spec.MlKem1024.encapsContract, Spec.MlKem1024.encapsSig, encapsAArch64, lay1024,
      KemLay.params, Spec.MlKem.mlKem1024, KemLay.ekLen, KemLay.ctLen, AArch64.abi, AArch64.argRegs] [sat]
      using sat)

theorem encaps_verified :
    Verified AArch64.target encaps (Spec.MlKem1024.encapsContract AArch64.abi 16) :=
  encaps_verifiedWith (keccak := .scalar)

end VG.Proof.MlKem1024.AArch64.Encaps
