import VerifiedGarbage.Proof.Argon2.X86_64.AddressCallsStage
import VerifiedGarbage.Proof.Argon2.X86_64.ClearBlock

/-! Clear an address-generation block, retaining the allocation invariants. -/

namespace VG.Proof.Argon2.X86_64.AddressCalls

open VG VG.X86_64 VG.Spec.Argon2 VG.Impl.Argon2.X86_64.AddressCalls

structure Cleared (s t : State) (offset : Nat) : Prop where
  block : blockAt t.mem (off (work s) offset) = zeroBlock
  ready : Ready t
  work_eq : work t = work s
  regs : ∀ r ∈ calleeSaved, t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  frame : Frame [⟨off (work s) offset, 1024⟩] s.mem t.mem
  mxcsr : t.mxcsr = s.mxcsr

theorem clearAt_ok (s : State) (h : Ready s) (offset : Nat) (bound : offset + 1024 ≤ 8192) :
    WP isa (clearAt offset) s (Cleared s · offset) := by
  unfold clearAt
  refine WP.seq ((pointer_ok s offset h.frameRead).mono ?_)
  rintro a ⟨dest, keeps⟩
  rw [displacement_eq offset (by omega)] at dest
  have write : Covers [⟨a.gpr .rdi, 1024⟩] a.wr := by
    rw [dest, keeps.wr]; exact work_cover s h offset 1024 bound
  refine (ClearBlock.code_ok a write).mono ?_
  rintro t ⟨zero, frame, tk, mx⟩
  have regs : ∀ r ∈ calleeSaved, t.gpr r = s.gpr r := by
    intro r hr
    have ne : r ≠ .rax ∧ r ≠ .rdi := by
      simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    exact (tk.1 r ne.1).trans (keeps.regs r (by simpa only [List.mem_cons, List.not_mem_nil, or_false] using ne.2))
  have rd := tk.2.1.trans keeps.rd
  have wr := tk.2.2.trans keeps.wr
  have hf : Frame [⟨off (work s) offset, 1024⟩] s.mem t.mem := by
    rw [dest, keeps.mem] at frame; exact frame
  have bigger : Frame (stageWrites s offset) s.mem t.mem :=
    hf.mono (by
      intro r hr
      simp only [List.mem_singleton] at hr
      subst r
      simp [stageWrites])
  obtain ⟨ready, work'⟩ := ready_of_frame h offset bound regs rd wr bigger
  rw [dest] at zero
  exact ⟨zero, ready, work', regs, rd, wr, hf, mx.trans keeps.mxcsr⟩

theorem Cleared.full_frame {s t : State} {offset : Nat} (h : Cleared s t offset)
    (bound : offset + 1024 ≤ 8192) : Frame [⟨work s, 8192⟩] s.mem t.mem := by
  apply h.frame.sub
  intro r hr
  simp only [List.mem_singleton] at hr
  subst r
  exact ⟨⟨work s, 8192⟩, by simp, Offset.sub_base _ bound⟩

theorem frame_word {s t : State} (h : Ready s) (frame : Frame [⟨work s, 8192⟩] s.mem t.mem)
    (d : Nat) (bound : d + 8 ≤ 272) :
    t.mem.readW (off (s.gpr .rbp) d) 64 = s.mem.readW (off (s.gpr .rbp) d) 64 :=
  frame.readW (r := ⟨s.gpr .rbp, 272⟩) (Offset.contains_base _ bound (by omega))
    (by intro r hr; simp only [List.mem_singleton] at hr; subst r; exact h.frameWork) (by decide)

end VG.Proof.Argon2.X86_64.AddressCalls
