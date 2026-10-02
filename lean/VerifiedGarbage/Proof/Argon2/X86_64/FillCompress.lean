import VerifiedGarbage.Proof.Argon2.X86_64.FillCompressSetup
import VerifiedGarbage.Proof.Argon2.X86_64.FillCompressLit

/-! The complete compression/update sequence from allocation and frame invariants. -/

namespace VG.Proof.Argon2.X86_64.FillCompress

open VG VG.X86_64 VG.Spec.Argon2 VG.Impl.Argon2.X86_64.FillCompress

def writes (s : State) : List Region :=
  [⟨s.gpr .r10, 1024⟩, ⟨work s + 4096, 1024⟩, ⟨work s, 4096⟩,
    below (s.gpr .rsp) 8, ⟨off (s.gpr .rbp) 16, 8⟩]

structure Done (s t : State) : Prop where
  block : blockAt t.mem (s.gpr .r10) =
    let next := Spec.Argon2.compress (blockAt s.mem (s.gpr .rdi)) (blockAt s.mem (s.gpr .rsi))
    if pass s = 0 then next else xorBlock next (blockAt s.mem (s.gpr .r10))
  regs : ∀ r ∈ calleeSaved, t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  frame : Frame (writes s) s.mem t.mem

theorem code_ok (s : State) (h : Ready s) : WP isa code s (Done s) := by
  unfold code
  refine WP.seq ((setup_ok s h).mono ?_)
  intro a prepared
  refine (operation_ok a prepared.ready).mono ?_
  intro t done
  refine ⟨?_, fun r hr => (done.regs r hr).trans (prepared.regs r hr),
    done.rd.trans prepared.rd, done.wr.trans prepared.wr, ?_⟩
  · have block := done.block
    rw [prepared.oldBlock, prepared.dest, prepared.counter, prepared.leftBlock,
      prepared.rightBlock] at block
    exact block
  · have frame : Frame (writes s) a.mem t.mem := by
      have original := done.frame
      rw [prepared.dest] at original
      simp only [callWrites, prepared.output, prepared.scratch,
        prepared.regs .rsp (by simp [calleeSaved])] at original
      exact original.mono (by intro r hr; exact List.mem_append_left _ hr)
    have savedFrame : Frame (writes s) s.mem a.mem := prepared.frame.mono (by
      intro r hr
      simp only [prefixWrites, List.mem_singleton] at hr
      subst r
      simp [writes])
    exact savedFrame.trans frame

theorem code_mx_ok (s : State) (h : Ready s) :
    WP isa code s fun t => Done s t ∧ t.mxcsr = s.mxcsr :=
  WP.mono_mx (by lit_decide) (code_ok s h) (fun _ done mx => ⟨done, mx⟩)

end VG.Proof.Argon2.X86_64.FillCompress
