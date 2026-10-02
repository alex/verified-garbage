import VerifiedGarbage.Proof.TripleDes.X86.Key.Pre

namespace VG.Proof.TripleDes.X86.Key
open VG VG.X86
open VG.Proof.Rc2.X86 (addr32)

theorem expand_correct (s : State) (hs : contract.pre s) :
    WP isa Impl.TripleDes.X86.Key.expandKey s (fun s' => abiPreserved s s' ∧ contract.post s s') := by
  have hp := headPre_of_contract s hs
  obtain ⟨_, _, _, _, _, _, _, retOutput, retScratch, _⟩ := hs
  apply WP.mono (expandKey_ok s hp)
  intro s' hpost
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro r hr
    have regs : ∀ r ∈ calleeSaved, r ∈ Impl.TripleDes.X86.savedRegs ∨ r = .esp := by decide
    rcases regs r hr with saved | rfl
    · exact hpost.saved r saved
    · exact hpost.sp
  · apply hpost.frame.readW (r := ⟨addr32 (s.gpr .esp), 4⟩) (Region.contains_self _ _) _ (by decide)
    intro r hr
    rcases List.mem_cons.mp hr with rfl | hr
    · rw [outputR, output_argument]; exact retOutput
    · obtain rfl := List.mem_singleton.mp hr
      rw [scratchR, scratch_argument]; exact retScratch
  · have result := hpost.result
    rw [output_argument, key_argument, keyLength] at result
    exact result

end VG.Proof.TripleDes.X86.Key
