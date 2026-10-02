import VerifiedGarbage.Proof.AesGcm.Arm.InitCT
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Arm.Contract

/-!
# AES-GCM on ARMv7: `Verified`

Untrusted: everything here is checked by Lean. Correctness and constant
time, a state satisfying each precondition, and the shared contracts of
`Spec/Gcm/Contract.lean`, with 8 bytes of stack: each call of
`vg_aes_ctr32` or `vg_ghash` pushes two words.
-/

namespace VG.Proof.AesGcm.Arm

open VG VG.Arm VG.Impl.AesGcm.Arm

/-- A state with the given registers, the stack pointer at `0x8000`, memory
of zeros (so stack arguments of 0) and the given regions. -/
def mkSat (g : Reg → BitVec 32) (rd wr : List Region) : State where
  gpr := g
  sp := 0x8000
  n := false
  z := false
  c := false
  v := false
  mem _ := 0
  rd := rd
  wr := wr

/-- A state satisfying `vg_aes_gcm_init`'s precondition. -/
def initSat : State :=
  mkSat (fun r => match r with | .r0 => 0x1000 | .r1 => 16 | .r2 => 0x2000 | .r3 => 0x3000 | _ => 0)
    [⟨0x1000, 16⟩] [⟨0x2000, 256⟩, ⟨0x3000, 2560⟩]

theorem init_verified : Verified Arm.target init (Spec.Gcm.initContract Arm.abi 8) :=
  Verified.of_correct (fun _ hs => init_wp hs) init_ct (by
    sig_implies [Spec.Gcm.initContract, Spec.Gcm.initSig, initArm, bel, Arm.abi, Arm.argRegs,
      Arm.reduceClassify, Arm.Loc.val, Arm.State.addr] [initSat, mkSat] using initSat)

end VG.Proof.AesGcm.Arm
