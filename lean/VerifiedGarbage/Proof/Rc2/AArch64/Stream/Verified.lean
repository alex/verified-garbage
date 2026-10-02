import VerifiedGarbage.Proof.Rc2.AArch64.Stream.Init
import VerifiedGarbage.Proof.Rc2.AArch64.Stream.Update
import VerifiedGarbage.Proof.Rc2.AArch64.Stream.ConstantTime
import VerifiedGarbage.Proof.Framework.Contract

/-!
# Verified streaming RC2-CBC on AArch64

Correctness (`Init`, `Update`), constant time (`ConstantTime`), and states
satisfying the preconditions, moved to the shared contracts with `stack = 16`
(the frame saving `x30`).
-/

namespace VG.Proof.Rc2.AArch64.Stream

open VG VG.AArch64 VG.Impl.Rc2.AArch64.Stream

def initSat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x3 => 0x2000 | .x5 => 0x3000 | .x6 => 0x4000 | _ => 0
  sp := 0x6000
  mem _ := 0
  rd := [⟨0x1000, 0⟩, ⟨0x2000, 0⟩]
  wr := [⟨0x3000, 144⟩, ⟨0x4000, 576⟩]

def updateSat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x2 => 0x2000 | .x4 => 0x3000 | .x6 => 0x4000 | _ => 0
  sp := 0x6000
  mem _ := 0
  rd := [⟨0x2000, 0⟩]
  wr := [⟨0x1000, 144⟩, ⟨0x3000, 0⟩, ⟨0x4000, 576⟩]

theorem publicRegs_seven (s₁ s₂ : State) : PublicRegs [.x0, .x1, .x2, .x3, .x4, .x5, .x6] s₁ s₂ ↔
    s₁.sp = s₂.sp ∧ s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.gpr .x2 = s₂.gpr .x2 ∧
    s₁.gpr .x3 = s₂.gpr .x3 ∧ s₁.gpr .x4 = s₂.gpr .x4 ∧ s₁.gpr .x5 = s₂.gpr .x5 ∧
    s₁.gpr .x6 = s₂.gpr .x6 := by
  simp [PublicRegs]

theorem init_correct' (s : State) (hs : initContract.pre s) :
    ∃ t s', Exec isa init s t s' ∧ abiPreserved s s' ∧ initContract.post s s' :=
  WP.withPreservedV (init_correct s hs) (by lit_decide)

theorem encryptUpdate_correct (s : State) (hs : (updateContract .encrypt).pre s) :
    ∃ t s', Exec isa encryptUpdate s t s' ∧ abiPreserved s s' ∧ (updateContract .encrypt).post s s' :=
  WP.withPreservedV (update_correct .encrypt s hs)
    (by lit_decide)

theorem decryptUpdate_correct (s : State) (hs : (updateContract .decrypt).pre s) :
    ∃ t s', Exec isa decryptUpdate s t s' ∧ abiPreserved s s' ∧ (updateContract .decrypt).post s s' :=
  WP.withPreservedV (update_correct .decrypt s hs)
    (by lit_decide)

theorem init_verified : Verified target init (Spec.Rc2.cbcInitContract abi 16) := by
  refine Verified.of_correct init_correct' (init_constantTime _) ?_
  sig_implies [Spec.Rc2.cbcInitContract, Spec.Rc2.cbcInitSig, abi, argRegs, initContract,
    publicRegs_seven] [initSat] using initSat

theorem encryptUpdate_verified :
    Verified target encryptUpdate (Spec.Rc2.cbcEncryptUpdateContract abi 16) := by
  refine Verified.of_correct encryptUpdate_correct (encryptUpdate_constantTime _) ?_
  sig_implies [Spec.Rc2.cbcEncryptUpdateContract, Spec.Rc2.cbcUpdateContract, Spec.Rc2.cbcUpdateSig,
    abi, argRegs, updateContract, publicRegs_seven] [updateSat] using updateSat

theorem decryptUpdate_verified :
    Verified target decryptUpdate (Spec.Rc2.cbcDecryptUpdateContract abi 16) := by
  refine Verified.of_correct decryptUpdate_correct (decryptUpdate_constantTime _) ?_
  sig_implies [Spec.Rc2.cbcDecryptUpdateContract, Spec.Rc2.cbcUpdateContract, Spec.Rc2.cbcUpdateSig,
    abi, argRegs, updateContract, publicRegs_seven] [updateSat] using updateSat

end VG.Proof.Rc2.AArch64.Stream
