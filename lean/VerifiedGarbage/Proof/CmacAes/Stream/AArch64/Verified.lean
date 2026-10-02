import VerifiedGarbage.Proof.CmacAes.Stream.AArch64.Init
import VerifiedGarbage.Proof.CmacAes.Stream.AArch64.AbsorbCT
import VerifiedGarbage.Proof.CmacAes.Stream.AArch64.Finish
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Spec.Cmac.Contract

/-!
# Streaming AES-CMAC on AArch64: `Verified`

Correctness and constant time (for any implementation `v` of AES), a state
satisfying each precondition, and the shared contracts of
`Spec/Cmac/Contract.lean` (with no stack: the calls keep the return address in
`x30`, which each function saves in the scratch buffer).
-/

namespace VG.Proof.CmacAes.Stream.AArch64

open VG VG.AArch64 VG.Impl.CmacAes.Stream.AArch64
open VG.Proof.Aes.AArch64 (Ctr32Impl)
open VG.Proof.CmacAes.AArch64 (update_keepsV subkeys_keepsV finalize_keepsV)

theorem init_keepsV (v : Ctr32Impl) : (init v.expand v.callee v.suffix).allInstrs keepsV = true := by
  simp only [init, Code.allInstrs, v.expandKeepsV, subkeys_keepsV v]; decide +kernel

theorem absorb_keepsV (v : Ctr32Impl) : (absorb v.callee v.suffix).allInstrs keepsV = true := by
  simp only [absorb, absorbPre, absorbPost, held, clamp, fill, copy, chain1, chain2, Code.allInstrs,
    update_keepsV v]
  decide +kernel

theorem finish_keepsV (v : Ctr32Impl) : (finish v.callee v.suffix).allInstrs keepsV = true := by
  simp only [finish, finPre, lastLen, Code.allInstrs, finalize_keepsV v]; decide +kernel

theorem init_correct (v : Ctr32Impl) (s : State) (hs : initAArch64.pre s) :
    ∃ t s', Exec isa (init v.expand v.callee v.suffix) s t s' ∧ abiPreserved s s' ∧ initAArch64.post s s' :=
  WP.withPreservedV (init_wp v hs) (init_keepsV v)

theorem absorb_correct (v : Ctr32Impl) (s : State) (hs : absorbAArch64.pre s) :
    ∃ t s', Exec isa (absorb v.callee v.suffix) s t s' ∧ abiPreserved s s' ∧ absorbAArch64.post s s' :=
  WP.withPreservedV (absorb_wp v hs) (absorb_keepsV v)

theorem finish_correct (v : Ctr32Impl) (s : State) (hs : finishAArch64.pre s) :
    ∃ t s', Exec isa (finish v.callee v.suffix) s t s' ∧ abiPreserved s s' ∧ finishAArch64.post s s' :=
  WP.withPreservedV (finish_wp v hs) (finish_keepsV v)

/-- A state satisfying `vg_cmac_aes_init`'s precondition. -/
def initSat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 0x3000 | .x2 => 16 | .x3 => 0x4000 | _ => 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x3000, 16⟩]
  wr := [⟨0x1000, 304⟩, ⟨0x4000, 2304⟩]

theorem init_verified (v : Ctr32Impl) :
    Verified AArch64.target (init v.expand v.callee v.suffix) (Spec.Cmac.aesInitContract AArch64.abi) :=
  Verified.of_correct (init_correct v) (init_ct v) (by
    sig_implies [Spec.Cmac.aesInitContract, Spec.Cmac.aesInitSig, initAArch64, AArch64.abi,
      AArch64.argRegs] [initSat] using initSat)

/-- A state satisfying `vg_cmac_aes_absorb`'s precondition (with no data). -/
def absorbSat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 10 | .x3 => 0x3000 | .x5 => 0x4000 | _ => 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x3000, 0⟩]
  wr := [⟨0x1000, 304⟩, ⟨0x4000, 2304⟩]

theorem absorb_verified (v : Ctr32Impl) :
    Verified AArch64.target (absorb v.callee v.suffix) (Spec.Cmac.aesAbsorbContract AArch64.abi) :=
  Verified.of_correct (absorb_correct v) (absorb_ct v) (by
    sig_implies [Spec.Cmac.aesAbsorbContract, Spec.Cmac.aesAbsorbSig, absorbAArch64, AArch64.abi,
      AArch64.argRegs] [absorbSat] using absorbSat)

/-- A state satisfying `vg_cmac_aes_finish`'s precondition. -/
def finishSat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 10 | .x3 => 0x2000 | .x4 => 0x4000 | _ => 0
  sp := 0x8000
  mem _ := 0
  rd := []
  wr := [⟨0x1000, 304⟩, ⟨0x2000, 16⟩, ⟨0x4000, 2304⟩]

theorem finish_verified (v : Ctr32Impl) :
    Verified AArch64.target (finish v.callee v.suffix) (Spec.Cmac.aesFinishContract AArch64.abi) :=
  Verified.of_correct (finish_correct v) (finish_ct v) (by
    sig_implies [Spec.Cmac.aesFinishContract, Spec.Cmac.aesFinishSig, finishAArch64, AArch64.abi,
      AArch64.argRegs] [finishSat] using finishSat)

end VG.Proof.CmacAes.Stream.AArch64
