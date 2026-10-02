import VerifiedGarbage.Proof.MlKem.X86_64.KgTop
import VerifiedGarbage.Proof.MlKem.X86_64.EcTop
import VerifiedGarbage.Proof.MlKem.X86_64.DcTop

/-!
# ML-KEM-768 on x86-64: `vg_mlkem768_keygen`, `vg_mlkem768_encaps` and `vg_mlkem768_decaps`

The proofs for any parameter set (`KgTop.lean`, `EcTop.lean`, `DcTop.lean`)
for ML-KEM-768 (`kem768`): its layout passes their checks, evaluated here,
it calls `vg_mlkem_compress_encode` and `vg_mlkem_decode_decompress` for its
widths, and the shared contracts imply the contracts the proofs are written
against.
-/

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64 VG.Impl.MlKem.X86_64
open VG.Spec.MlKem

theorem kemWf768 : KemWf kem768 := by kem_wf

theorem kgWf768 : KeyGen.KgWf kem768 := by kem_wf kemWf768
theorem ecWf768 : Encaps.EcWf kem768 := by kem_wf kemWf768
theorem dcWf768 : Decaps.DcWf kem768 := by kem_wf kemWf768

/-- The compressions it calls. -/
theorem calls768 : KemCalls kem768 compressWidths compressWidths := ⟨ceImpl, ddImpl, by decide, by decide⟩

/-- States satisfying the shared contracts' preconditions. -/
def keyGenSat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 0x2000 | .rdx => 0x3000 | .rcx => 0x10000 | .rsp => 0x80000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x1000, 64⟩]
  wr := [⟨0x2000, 1184⟩, ⟨0x3000, 2400⟩, ⟨0x10000, 32768⟩]

def encapsSat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 0x2000 | .rdx => 0x3000 | .rcx => 0x4000 | .r8 => 0x10000 | .rsp => 0x80000
    | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x1000, 1184⟩, ⟨0x2000, 32⟩]
  wr := [⟨0x3000, 32⟩, ⟨0x4000, 1088⟩, ⟨0x10000, 32768⟩]

def decapsSat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 0x2000 | .rdx => 0x3000 | .rcx => 0x10000 | .rsp => 0x80000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x1000, 2400⟩, ⟨0x2000, 1088⟩]
  wr := [⟨0x3000, 32⟩, ⟨0x10000, 32768⟩]

theorem keyGen_verified (v : Sample4Impl) :
    Verified X86_64.target (kemKeyGen kem768 v.callee) (Spec.MlKem.keyGenContract X86_64.abi 32) :=
  Verified.of_correct (kemKeyGen_correct v kgWf768 (by s4_ctl v)) (kemKeyGen_ct v kgWf768)
    { pre := by sig_implies_pre [Spec.MlKem.keyGenContract, Spec.MlKem.keyGenSig, keyGenK, X86_64.abi, VG.X86_64.argRegs, kem768, Kem.ekLen, Kem.dkLen, Kem.ctLen, Params.ekLen, Params.dkLen, Params.ctLen, mlKem768]
      post := by sig_implies_post [Spec.MlKem.keyGenContract, Spec.MlKem.keyGenSig, keyGenK, X86_64.abi, VG.X86_64.argRegs, kem768, Kem.ekLen, Kem.dkLen, Kem.ctLen, Params.ekLen, Params.dkLen, Params.ctLen, mlKem768]
      pub := by
        intro s₁ s₂ _ _ h
        sig_pub [Spec.MlKem.keyGenContract, Spec.MlKem.keyGenSig, keyGenK, X86_64.abi, VG.X86_64.argRegs] at h
        obtain ⟨hsp, hb, hdi, hsi, hdx, hcx⟩ := h
        exact ⟨hdi, hsi, hdx, hcx, hsp, map_toNat_inj hb⟩
      sat := by sig_implies_sat [Spec.MlKem.keyGenContract, Spec.MlKem.keyGenSig, keyGenK, X86_64.abi, VG.X86_64.argRegs, kem768, Kem.ekLen, Kem.dkLen, Kem.ctLen, Params.ekLen, Params.dkLen, Params.ctLen, mlKem768] [keyGenSat]
        using keyGenSat }

theorem encaps_verified (v : Sample4Impl) :
    Verified X86_64.target (kemEncaps kem768 v.callee) (Spec.MlKem.encapsContract X86_64.abi 32) :=
  Verified.of_correct (kemEncaps_correct v ecWf768 calls768 (by s4_ctl v)) (kemEncaps_ct v ecWf768 calls768)
    { pre := by sig_implies_pre [Spec.MlKem.encapsContract, Spec.MlKem.encapsSig, encapsK, X86_64.abi, VG.X86_64.argRegs, kem768, Kem.ekLen, Kem.dkLen, Kem.ctLen, Params.ekLen, Params.dkLen, Params.ctLen, mlKem768]
      post := by sig_implies_post [Spec.MlKem.encapsContract, Spec.MlKem.encapsSig, encapsK, X86_64.abi, VG.X86_64.argRegs, kem768, Kem.ekLen, Kem.dkLen, Kem.ctLen, Params.ekLen, Params.dkLen, Params.ctLen, mlKem768]
      pub := by
        intro s₁ s₂ _ _ h
        sig_pub [Spec.MlKem.encapsContract, Spec.MlKem.encapsSig, encapsK, X86_64.abi, VG.X86_64.argRegs] at h
        obtain ⟨hsp, hb, hdi, hsi, hdx, hcx, h8⟩ := h
        exact ⟨hdi, hsi, hdx, hcx, h8, hsp, map_toNat_inj hb⟩
      sat := by sig_implies_sat [Spec.MlKem.encapsContract, Spec.MlKem.encapsSig, encapsK, X86_64.abi, VG.X86_64.argRegs, kem768, Kem.ekLen, Kem.dkLen, Kem.ctLen, Params.ekLen, Params.dkLen, Params.ctLen, mlKem768] [encapsSat]
        using encapsSat }

theorem decaps_verified (v : Sample4Impl) :
    Verified X86_64.target (kemDecaps kem768 v.callee) (Spec.MlKem.decapsContract X86_64.abi 32) :=
  Verified.of_correct (kemDecaps_correct v dcWf768 calls768 (by s4_ctl v)) (kemDecaps_ct v dcWf768 calls768)
    { pre := by sig_implies_pre [Spec.MlKem.decapsContract, Spec.MlKem.decapsSig, decapsK, X86_64.abi, VG.X86_64.argRegs, kem768, Kem.ekLen, Kem.dkLen, Kem.ctLen, Params.ekLen, Params.dkLen, Params.ctLen, mlKem768]
      post := by sig_implies_post [Spec.MlKem.decapsContract, Spec.MlKem.decapsSig, decapsK, X86_64.abi, VG.X86_64.argRegs, kem768, Kem.ekLen, Kem.dkLen, Kem.ctLen, Params.ekLen, Params.dkLen, Params.ctLen, mlKem768]
      pub := by
        intro s₁ s₂ _ _ h
        sig_pub [Spec.MlKem.decapsContract, Spec.MlKem.decapsSig, decapsK, X86_64.abi, VG.X86_64.argRegs] at h
        obtain ⟨hsp, hb, hdi, hsi, hdx, hcx⟩ := h
        exact ⟨hdi, hsi, hdx, hcx, hsp, map_toNat_inj hb⟩
      sat := by sig_implies_sat [Spec.MlKem.decapsContract, Spec.MlKem.decapsSig, decapsK, X86_64.abi, VG.X86_64.argRegs, kem768, Kem.ekLen, Kem.dkLen, Kem.ctLen, Params.ekLen, Params.dkLen, Params.ctLen, mlKem768] [decapsSat]
        using decapsSat }

end VG.Proof.MlKem.X86_64
