import VerifiedGarbage.Proof.CmacTripleDes.X86_64.Contract
import VerifiedGarbage.Proof.Framework.Contract

/-!
# TDEA-CMAC on x86-64: the shared contracts imply ours
-/

namespace VG.Proof.CmacTripleDes.X86_64

open VG VG.X86_64

/-- A state satisfying `vg_cmac_triple_des_init`'s precondition. -/
def initSat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 16 | .rdx => 0x2000 | .rcx => 0x4000 | .rsp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x1000, 16⟩]
  wr := [⟨0x2000, 400⟩, ⟨0x4000, 640⟩]

theorem init_implies : initX86_64.Implies (Spec.Cmac.tdesInitContract X86_64.abi 0) := by
  sig_implies [Spec.Cmac.tdesInitContract, Spec.Cmac.tdesInitSig, initX86_64, X86_64.abi,
    X86_64.argRegs] [initSat] using initSat

/-- A state satisfying `vg_cmac_triple_des_update`'s precondition (with no blocks). -/
def updSat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 0x2000 | .rdx => 0x3000 | .r8 => 0x4000 | .rsp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x1000, 384⟩, ⟨0x3000, 0⟩]
  wr := [⟨0x2000, 8⟩, ⟨0x4000, 640⟩]

theorem update_implies : updateX86_64.Implies (Spec.Cmac.tdesUpdateContract X86_64.abi 0) := by
  sig_implies [Spec.Cmac.tdesUpdateContract, Spec.Cmac.tdesUpdateSig, updateX86_64, X86_64.abi,
    X86_64.argRegs] [updSat] using updSat

/-- A state satisfying `vg_cmac_triple_des_finalize`'s precondition (with no last bytes). -/
def finSat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 0x2000 | .rdx => 0x3000 | .r8 => 0x4000 | .rsp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x1000, 400⟩, ⟨0x3000, 0⟩]
  wr := [⟨0x2000, 8⟩, ⟨0x4000, 640⟩]

theorem finalize_implies : finalizeX86_64.Implies (Spec.Cmac.tdesFinalizeContract X86_64.abi 0) := by
  sig_implies [Spec.Cmac.tdesFinalizeContract, Spec.Cmac.tdesFinalizeSig, finalizeX86_64, X86_64.abi,
    X86_64.argRegs] [finSat] using finSat

end VG.Proof.CmacTripleDes.X86_64
