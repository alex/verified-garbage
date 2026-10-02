import VerifiedGarbage.Proof.TripleDes.X86_64.VerifiedBlock

namespace VG.Proof.TripleDes.X86_64

open VG VG.X86_64 VG.Impl.TripleDes.X86_64
open VG.Spec.TripleDes (Direction)

def strongBlockContract (d : Direction) : Contract isa where
  pre := (blockContract d).pre
  pub := (blockContract d).pub
  post s s' := BlockPost (Spec.TripleDes.scheduleAt s.mem (s.gpr .rdi)) d s s'

theorem strongBlock_correct (d : Direction) (s : State) (hs : (strongBlockContract d).pre s) :
    ∃ t s', Exec isa (block d) s t s' ∧ abiPreserved s s' ∧
      (strongBlockContract d).post s s' := by
  have hp := headPre_of_contract d s hs
  have hwrite : InRegions s.wr (s.gpr .rsi) 8 := by
    rw [hs.2.1]
    exact ⟨⟨s.gpr .rsi, 8⟩, by simp, Region.contains_self _ _⟩
  have hwp : WP isa (block d) s (fun s' => gprPreserved s s' ∧
      (strongBlockContract d).post s s') := by
    apply WP.mono (block_ok (Spec.TripleDes.scheduleAt s.mem (s.gpr .rdi)) (s.gpr .rdi) d s hp hwrite)
    intro s' hpost
    refine ⟨⟨?_, ?_⟩, hpost⟩
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
  obtain ⟨t, s', he, ha, hp⟩ := hwp
  refine ⟨t, s', he, abiPreserved_of_exec ?_ he ha, hp⟩
  cases d
  · change (encryptBlock.allInstrs (fun i => !loadsMxcsr i)) = true
    lit_decide
  · change (decryptBlock.allInstrs (fun i => !loadsMxcsr i)) = true
    lit_decide

end VG.Proof.TripleDes.X86_64
