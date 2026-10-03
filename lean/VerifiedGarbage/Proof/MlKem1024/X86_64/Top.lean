import VerifiedGarbage.Proof.MlKem.X86_64.KgTop
import VerifiedGarbage.Proof.MlKem.X86_64.EcTop
import VerifiedGarbage.Proof.MlKem.X86_64.DcTop
import VerifiedGarbage.Proof.MlKem1024.X86_64.CompressEncode
import VerifiedGarbage.Proof.MlKem1024.X86_64.DecodeDecompress
import VerifiedGarbage.Impl.MlKem1024.X86_64.Kem
import VerifiedGarbage.Spec.MlKem.Contract1024

/-!
# ML-KEM-1024 on x86-64: `vg_mlkem1024_keygen`, `vg_mlkem1024_encaps` and `vg_mlkem1024_decaps`

The proofs for any parameter set (`Proof/MlKem/X86_64/KgTop.lean`,
`EcTop.lean`, `DcTop.lean`) for ML-KEM-1024 (`kem1024`): its layout passes
their checks, evaluated here, it calls `vg_mlkem1024_compress_encode` and
`vg_mlkem1024_decode_decompress` for its widths, and the shared contracts
imply the contracts the proofs are written against.
-/

namespace VG.Proof.MlKem1024.X86_64

open VG VG.X86_64 VG.Impl.MlKem.X86_64 VG.Impl.MlKem1024.X86_64
open VG.Proof.MlKem VG.Proof.MlKem.X86_64
open VG.Spec.MlKem

theorem kemWf1024 : KemWf kem1024 := by kem_wf

theorem kgWf1024 : KeyGen.KgWf kem1024 := by kem_wf kemWf1024
theorem ecWf1024 : Encaps.EcWf kem1024 := by kem_wf kemWf1024
theorem dcWf1024 : Decaps.DcWf kem1024 := by kem_wf kemWf1024

/-- The compressions it calls. -/
theorem calls1024 : KemCalls kem1024 Spec.MlKem1024.compressWidths Spec.MlKem1024.compressWidths := ⟨ceImpl1024, ddImpl1024, by decide, by decide⟩

/-- States satisfying the shared contracts' preconditions. -/
def keyGen1024Sat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 0x2000 | .rdx => 0x3000 | .rcx => 0x10000 | .rsp => 0x80000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x1000, 64⟩]
  wr := [⟨0x2000, 1568⟩, ⟨0x3000, 3168⟩, ⟨0x10000, 49152⟩]

def encaps1024Sat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 0x2000 | .rdx => 0x3000 | .rcx => 0x4000 | .r8 => 0x10000 | .rsp => 0x80000
    | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x1000, 1568⟩, ⟨0x2000, 32⟩]
  wr := [⟨0x3000, 32⟩, ⟨0x4000, 1568⟩, ⟨0x10000, 49152⟩]

def decaps1024Sat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 0x2000 | .rdx => 0x3000 | .rcx => 0x10000 | .rsp => 0x80000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x1000, 3168⟩, ⟨0x2000, 1568⟩]
  wr := [⟨0x3000, 32⟩, ⟨0x10000, 49152⟩]

theorem keyGen1024_verified (v : Sample4Impl) :
    Verified X86_64.target (kemKeyGen kem1024 v.callee) (Spec.MlKem1024.keyGenContract X86_64.abi 32) :=
  Verified.of_correct (kemKeyGen_correct v kgWf1024 (by s4_ctl v)) (kemKeyGen_ct v kgWf1024)
    { pre := by sig_implies_pre [Spec.MlKem1024.keyGenContract, Spec.MlKem1024.keyGenSig, keyGenK, X86_64.abi, VG.X86_64.argRegs, kem1024, Kem.ekLen, Kem.dkLen, Kem.ctLen, Params.ekLen, Params.dkLen, Params.ctLen, mlKem1024]
      post := by sig_implies_post [Spec.MlKem1024.keyGenContract, Spec.MlKem1024.keyGenSig, keyGenK, X86_64.abi, VG.X86_64.argRegs, kem1024, Kem.ekLen, Kem.dkLen, Kem.ctLen, Params.ekLen, Params.dkLen, Params.ctLen, mlKem1024]
      pub := by
        intro s₁ s₂ _ _ h
        sig_pub [Spec.MlKem1024.keyGenContract, Spec.MlKem1024.keyGenSig, keyGenK, X86_64.abi, VG.X86_64.argRegs] at h
        obtain ⟨hsp, hb, hdi, hsi, hdx, hcx⟩ := h
        exact ⟨hdi, hsi, hdx, hcx, hsp, map_toNat_inj hb⟩
      sat := by sig_implies_sat [Spec.MlKem1024.keyGenContract, Spec.MlKem1024.keyGenSig, keyGenK, X86_64.abi, VG.X86_64.argRegs, kem1024, Kem.ekLen, Kem.dkLen, Kem.ctLen, Params.ekLen, Params.dkLen, Params.ctLen, mlKem1024] [keyGen1024Sat]
        using keyGen1024Sat }

theorem encaps1024_verified (v : Sample4Impl) :
    Verified X86_64.target (kemEncaps kem1024 v.callee) (Spec.MlKem1024.encapsContract X86_64.abi 32) :=
  Verified.of_correct (kemEncaps_correct v ecWf1024 calls1024 (by s4_ctl v)) (kemEncaps_ct v ecWf1024 calls1024)
    { pre := by sig_implies_pre [Spec.MlKem1024.encapsContract, Spec.MlKem1024.encapsSig, encapsK, X86_64.abi, VG.X86_64.argRegs, kem1024, Kem.ekLen, Kem.dkLen, Kem.ctLen, Params.ekLen, Params.dkLen, Params.ctLen, mlKem1024]
      post := by sig_implies_post [Spec.MlKem1024.encapsContract, Spec.MlKem1024.encapsSig, encapsK, X86_64.abi, VG.X86_64.argRegs, kem1024, Kem.ekLen, Kem.dkLen, Kem.ctLen, Params.ekLen, Params.dkLen, Params.ctLen, mlKem1024]
      pub := by
        intro s₁ s₂ _ _ h
        sig_pub [Spec.MlKem1024.encapsContract, Spec.MlKem1024.encapsSig, encapsK, X86_64.abi, VG.X86_64.argRegs] at h
        obtain ⟨hsp, hb, hdi, hsi, hdx, hcx, h8⟩ := h
        exact ⟨hdi, hsi, hdx, hcx, h8, hsp, map_toNat_inj hb⟩
      sat := by sig_implies_sat [Spec.MlKem1024.encapsContract, Spec.MlKem1024.encapsSig, encapsK, X86_64.abi, VG.X86_64.argRegs, kem1024, Kem.ekLen, Kem.dkLen, Kem.ctLen, Params.ekLen, Params.dkLen, Params.ctLen, mlKem1024] [encaps1024Sat]
        using encaps1024Sat }

theorem decaps1024_verified (v : Sample4Impl) :
    Verified X86_64.target (kemDecaps kem1024 v.callee) (Spec.MlKem1024.decapsContract X86_64.abi 32) :=
  Verified.of_correct (kemDecaps_correct v dcWf1024 calls1024 (by s4_ctl v)) (kemDecaps_ct v dcWf1024 calls1024)
    { pre := by sig_implies_pre [Spec.MlKem1024.decapsContract, Spec.MlKem1024.decapsSig, decapsK, X86_64.abi, VG.X86_64.argRegs, kem1024, Kem.ekLen, Kem.dkLen, Kem.ctLen, Params.ekLen, Params.dkLen, Params.ctLen, mlKem1024]
      post := by sig_implies_post [Spec.MlKem1024.decapsContract, Spec.MlKem1024.decapsSig, decapsK, X86_64.abi, VG.X86_64.argRegs, kem1024, Kem.ekLen, Kem.dkLen, Kem.ctLen, Params.ekLen, Params.dkLen, Params.ctLen, mlKem1024]
      pub := by
        intro s₁ s₂ _ _ h
        sig_pub [Spec.MlKem1024.decapsContract, Spec.MlKem1024.decapsSig, decapsK, X86_64.abi, VG.X86_64.argRegs] at h
        obtain ⟨hsp, hb, hdi, hsi, hdx, hcx⟩ := h
        exact ⟨hdi, hsi, hdx, hcx, hsp, map_toNat_inj hb⟩
      sat := by sig_implies_sat [Spec.MlKem1024.decapsContract, Spec.MlKem1024.decapsSig, decapsK, X86_64.abi, VG.X86_64.argRegs, kem1024, Kem.ekLen, Kem.dkLen, Kem.ctLen, Params.ekLen, Params.dkLen, Params.ctLen, mlKem1024] [decaps1024Sat]
        using decaps1024Sat }

end VG.Proof.MlKem1024.X86_64
