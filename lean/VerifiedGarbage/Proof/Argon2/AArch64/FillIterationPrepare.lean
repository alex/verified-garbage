import VerifiedGarbage.Impl.Argon2.AArch64.FillIteration
import VerifiedGarbage.Proof.Argon2.AArch64.FillSlices

/-! Start a pass at slice zero regardless of its incoming lane and slice coordinates. -/

namespace VG.Proof.Argon2.AArch64.FillIteration

open VG VG.AArch64 VG.Spec.Argon2

structure Ready (p : Params) (pass : Nat) (s : State) : Prop where
  parameters : FillContext.Parameters p pass 0 0
  header : ∃ lane slice, FillHeader.Ready p pass lane slice s

structure Prepared (s t : State) (p : Params) (pass : Nat) : Prop where
  ready : FillSlice.Ready p pass 0 t
  keeps : Divide.Keeps [.x22] s t

theorem setup_ok (s : State) (p : Params) (pass : Nat) (h : Ready p pass s) :
    WP isa (.block Impl.Argon2.AArch64.FillIteration.setup) s (Prepared s · p pass) := by
  refine (SegmentSetup.register_ok s .x22 0 (by decide)).mono ?_
  rintro t ⟨sliceWord, keeps⟩
  obtain ⟨lane, slice, header⟩ := h.header
  obtain ⟨old, words⟩ := header.words
  have next : FillHeader.Ready p pass lane 0 t := header.of_state (by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact keeps.regs _ (by decide))
    keeps.sp keeps.mem keeps.rd keeps.wr ((keeps.regs .x24 (by decide)).trans words.laneWord) sliceWord
  exact ⟨⟨h.parameters, lane, next⟩, keeps⟩

end VG.Proof.Argon2.AArch64.FillIteration
