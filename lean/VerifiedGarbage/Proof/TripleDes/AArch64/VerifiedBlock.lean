import VerifiedGarbage.Proof.TripleDes.AArch64.Pre
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Spec.TripleDes.Contract

namespace VG.Proof.TripleDes.AArch64

open VG VG.AArch64 VG.Impl.TripleDes.AArch64
open VG.Spec.TripleDes (Direction)

theorem block_gprCorrect (d : Direction) (s : State) (hs : (blockContract d).pre s) :
    WP isa (block d) s (fun s' => GprAbi s s' ∧ (blockContract d).post s s') := by
  have hp := headPre_of_contract d s hs
  have hwrite : InRegions s.wr (s.gpr .x1) 8 := by
    rw [hs.2.1]
    exact ⟨⟨s.gpr .x1, 8⟩, by simp, Region.contains_self _ _⟩
  apply WP.mono (block_ok (Spec.TripleDes.scheduleAt s.mem (s.gpr .x0)) (s.gpr .x0) d s hp hwrite)
  intro s' hpost
  refine ⟨⟨?_, hpost.sp⟩, hpost.result⟩
  intro r hr
  have hkeep : ∀ q ∈ preserved, q ∈ savedRegs ∨ q ∈ roundStepKept := by decide
  rcases hkeep r hr with h | h
  · exact hpost.saved r h
  · exact hpost.regs r h

theorem encrypt_correct (s : State) (hs : (blockContract .encrypt).pre s) :
    ∃ t s', Exec isa encryptBlock s t s' ∧ abiPreserved s s' ∧
      (blockContract .encrypt).post s s' := by
  obtain ⟨t, s', he, ha, hp⟩ := block_gprCorrect .encrypt s hs
  change Exec isa encryptBlock s t s' at he
  exact ⟨t, s', he, ⟨ha.1, ha.2, VG.AArch64.Exec.preservedV he (by lit_decide)⟩, hp⟩

theorem decrypt_correct (s : State) (hs : (blockContract .decrypt).pre s) :
    ∃ t s', Exec isa decryptBlock s t s' ∧ abiPreserved s s' ∧
      (blockContract .decrypt).post s s' := by
  obtain ⟨t, s', he, ha, hp⟩ := block_gprCorrect .decrypt s hs
  change Exec isa decryptBlock s t s' at he
  exact ⟨t, s', he, ⟨ha.1, ha.2, VG.AArch64.Exec.preservedV he (by lit_decide)⟩, hp⟩

def satState : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 0x2000 | .x2 => 0x3000 | _ => 0
  sp := 0x4000
  mem _ := 0
  rd := [⟨0x1000, 384⟩]
  wr := [⟨0x2000, 8⟩, ⟨0x3000, 512⟩]

theorem publicRegs_three (s t : State) : PublicRegs [.x0, .x1, .x2] s t ↔
    s.sp = t.sp ∧ s.gpr .x0 = t.gpr .x0 ∧ s.gpr .x1 = t.gpr .x1 ∧ s.gpr .x2 = t.gpr .x2 := by
  simp [PublicRegs]

theorem encrypt_verified : Verified target encryptBlock (Spec.TripleDes.encryptBlockContract abi) := by
  refine Verified.of_correct encrypt_correct
    (encryptBlock_constantTime _) ?_
  sig_implies [Spec.TripleDes.encryptBlockContract, Spec.TripleDes.blockSig, abi, argRegs,
    blockContract, publicRegs_three, blockResult] [satState] using satState

theorem decrypt_verified : Verified target decryptBlock (Spec.TripleDes.decryptBlockContract abi) := by
  refine Verified.of_correct decrypt_correct
    (decryptBlock_constantTime _) ?_
  sig_implies [Spec.TripleDes.decryptBlockContract, Spec.TripleDes.blockSig, abi, argRegs,
    blockContract, publicRegs_three, blockResult] [satState] using satState

end VG.Proof.TripleDes.AArch64
