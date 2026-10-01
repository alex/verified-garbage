import VerifiedGarbage.Proof.TripleDes.X86_64.Pre
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Spec.TripleDes.Contract

namespace VG.Proof.TripleDes.X86_64

open VG VG.X86_64 VG.Impl.TripleDes.X86_64
open VG.Spec.TripleDes (Direction)

theorem block_gprCorrect (d : Direction) (s : State) (hs : (blockContract d).pre s) :
    WP isa (block d) s (fun s' => gprPreserved s s' ∧ (blockContract d).post s s') := by
  have hp := headPre_of_contract d s hs
  have hwrite : InRegions s.wr (s.gpr .rsi) 8 := by
    rw [hs.2.1]
    exact ⟨⟨s.gpr .rsi, 8⟩, by simp, Region.contains_self _ _⟩
  apply WP.mono (block_ok (Spec.TripleDes.scheduleAt s.mem (s.gpr .rdi)) (s.gpr .rdi) d s hp hwrite)
  intro s' hpost
  refine ⟨⟨?_, ?_⟩, hpost.result⟩
  · intro r hr
    have hkeep : ∀ q ∈ calleeSaved,
        q ∈ savedRegs ++ [Reg.rdi] ∨ q ∈ [Reg.rsi, .rdx, .rsp] := by decide
    rcases hkeep r hr with h | h
    · exact hpost.saved r h
    · exact hpost.regs r h
  · apply hpost.frame.readW (r := ⟨s.gpr .rsp, 8⟩) (Region.contains_self _ _) _ (by decide)
    intro r hr
    simp only [blockRegions, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hs.2.2.2.2.1
    · exact hs.2.2.2.2.2

theorem encrypt_correct (s : State) (hs : (blockContract .encrypt).pre s) :
    ∃ t s', Exec isa encryptBlock s t s' ∧ abiPreserved s s' ∧
      (blockContract .encrypt).post s s' := by
  obtain ⟨t, s', he, ha, hp⟩ := block_gprCorrect .encrypt s hs
  change Exec isa encryptBlock s t s' at he
  exact ⟨t, s', he, abiPreserved_of_exec (by lit_decide) he ha, hp⟩

theorem decrypt_correct (s : State) (hs : (blockContract .decrypt).pre s) :
    ∃ t s', Exec isa decryptBlock s t s' ∧ abiPreserved s s' ∧
      (blockContract .decrypt).post s s' := by
  obtain ⟨t, s', he, ha, hp⟩ := block_gprCorrect .decrypt s hs
  change Exec isa decryptBlock s t s' at he
  exact ⟨t, s', he, abiPreserved_of_exec (by lit_decide) he ha, hp⟩

def satState : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 0x2000 | .rdx => 0x3000 | .rsp => 0x4000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x1000, 384⟩]
  wr := [⟨0x2000, 8⟩, ⟨0x3000, 512⟩]

theorem publicRegs_three (s t : State) : PublicRegs [.rdi, .rsi, .rdx] s t ↔
    s.gpr .rdi = t.gpr .rdi ∧ s.gpr .rsi = t.gpr .rsi ∧ s.gpr .rdx = t.gpr .rdx := by
  simp [PublicRegs]

theorem encrypt_verified : Verified target encryptBlock (Spec.TripleDes.encryptBlockContract abi) := by
  refine Verified.of_correct encrypt_correct
    (encryptBlock_constantTime _ _ (blockTaint_agree .encrypt)) ?_
  sig_implies [Spec.TripleDes.encryptBlockContract, Spec.TripleDes.blockSig, abi, argRegs,
    blockContract, publicRegs_three, blockResult] [satState] using satState

theorem decrypt_verified : Verified target decryptBlock (Spec.TripleDes.decryptBlockContract abi) := by
  refine Verified.of_correct decrypt_correct
    (decryptBlock_constantTime _ _ (blockTaint_agree .decrypt)) ?_
  sig_implies [Spec.TripleDes.decryptBlockContract, Spec.TripleDes.blockSig, abi, argRegs,
    blockContract, publicRegs_three, blockResult] [satState] using satState

end VG.Proof.TripleDes.X86_64
