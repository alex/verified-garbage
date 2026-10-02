import VerifiedGarbage.Proof.Argon2.AArch64.AddressCallsPrepare
import VerifiedGarbage.Proof.Argon2.AArch64.AddressCalls

/-! Complete independent-address generation against the reviewed algorithm. -/

namespace VG.Proof.Argon2.AArch64.AddressCalls

open VG VG.AArch64 VG.Spec.Argon2 VG.Impl.Argon2.AArch64.AddressCalls

theorem calls_sp_ok (p : Params) (pass lane slice counter : Nat) (s : State) (h : Ready s)
    (zero : blockAt s.mem (off (work s) 7168) = zeroBlock)
    (input : blockAt s.mem (off (work s) 5120) = Proof.Argon2.addressInput p pass lane slice counter) :
    WP isa calls s fun t => Generated s t p pass lane slice counter ∧ t.sp = s.sp :=
  (calls_ok p pass lane slice counter s h zero input).mono (fun _ h => ⟨h, h.sp⟩)

theorem code_ok (p : Params) (pass lane slice counter : Nat) (s : State) (h : Ready s)
    (reads : ∀ d ∈ [0, 8, 72, 112, 240], InRegions (s.rd ++ s.wr) (off (s.gpr .x19) d) 8)
    (words : AddressHeader.Words p pass lane slice counter s) :
    WP isa code s fun t => Generated s t p pass lane slice counter ∧ t.sp = s.sp := by
  unfold code
  refine WP.seq ((prepare_ok p pass lane slice counter s h reads words).mono ?_)
  intro a prepared
  have zero : blockAt a.mem (off (work a) 7168) = zeroBlock := by
    rw [prepared.stable.work_eq]; exact prepared.zero
  have input : blockAt a.mem (off (work a) 5120) = Proof.Argon2.addressInput p pass lane slice counter := by
    rw [prepared.stable.work_eq]; exact prepared.input
  refine (calls_sp_ok p pass lane slice counter a prepared.stable.ready zero input).mono ?_
  rintro t ⟨generated, mx⟩
  have frame := generated.frame
  rw [writes, prepared.stable.work_eq, prepared.stable.sp] at frame
  have firstFrame : Frame (writes s) s.mem a.mem :=
    prepared.stable.frame.mono (by
      intro r hr
      simp only [List.mem_singleton] at hr
      subst r
      simp [writes])
  refine ⟨⟨?_, generated.ready, generated.work.trans prepared.stable.work_eq,
    fun r hr => (generated.regs r hr).trans (prepared.stable.regs r hr),
    generated.rd.trans prepared.stable.rd, generated.wr.trans prepared.stable.wr, generated.sp.trans prepared.stable.sp,
    firstFrame.trans frame⟩, mx.trans prepared.stable.sp⟩
  have block := generated.block
  rw [prepared.stable.work_eq] at block
  exact block

end VG.Proof.Argon2.AArch64.AddressCalls
