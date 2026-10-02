import VerifiedGarbage.Proof.TripleDes.Arm.Key.Correct
import VerifiedGarbage.Proof.Framework.Contract

namespace VG.Proof.TripleDes.Arm.Key

open VG VG.Arm

def satState : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 16 | .r2 => 0x2000 | .r3 => 0x3000 | _ => 0
  sp := 0x4000
  n := false
  z := false
  c := false
  v := false
  mem _ := 0
  rd := [⟨0x1000, 16⟩]
  wr := [⟨0x2000, 384⟩, ⟨0x3000, 512⟩]

theorem correct (s : State) (hs : contract.pre s) :
    ∃ t s', Exec isa Impl.TripleDes.Arm.Key.expandKey s t s' ∧ abiPreserved s s' ∧ contract.post s s' := by
  obtain ⟨t, s', he, ha, hp⟩ := expand_correct s hs
  exact ⟨t, s', he, ⟨ha, VG.Arm.Exec.sp he⟩, hp⟩

theorem publicRegs_four (s₁ s₂ : State) : PublicRegs [.r0, .r1, .r2, .r3] s₁ s₂ ↔
    s₁.sp = s₂.sp ∧ s₁.gpr .r0 = s₂.gpr .r0 ∧ s₁.gpr .r1 = s₂.gpr .r1 ∧ s₁.gpr .r2 = s₂.gpr .r2 ∧
    s₁.gpr .r3 = s₂.gpr .r3 := by simp [PublicRegs]

theorem verified : Verified target Impl.TripleDes.Arm.Key.expandKey
    (Spec.TripleDes.expandKeyContract abi) := by
  refine Verified.of_correct correct (expandKey_constantTime _) ?_
  sig_implies [Spec.TripleDes.expandKeyContract, Spec.TripleDes.expandKeySig, abi, argRegs, Arm.reduceClassify, Arm.Loc.val, State.addr,
    contract, publicRegs_four] [satState] using satState

end VG.Proof.TripleDes.Arm.Key
