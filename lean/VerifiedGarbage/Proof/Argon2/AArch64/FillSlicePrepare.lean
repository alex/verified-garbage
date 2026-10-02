import VerifiedGarbage.Impl.Argon2.AArch64.FillSlice
import VerifiedGarbage.Proof.Argon2.AArch64.FillHeader

/-! Initialize lane zero without requiring a valid incoming lane coordinate. -/

namespace VG.Proof.Argon2.AArch64.FillSlice

open VG VG.AArch64 VG.Spec.Argon2

structure Ready (p : Params) (pass slice : Nat) (s : State) : Prop where
  parameters : FillContext.Parameters p pass 0 slice
  header : ∃ lane, FillHeader.Ready p pass lane slice s

structure Prepared (s t : State) (p : Params) (pass slice : Nat) : Prop where
  ready : SegmentSetup.Ready p pass 0 slice t
  keeps : Divide.Keeps [.x24] s t

theorem setup_ok (s : State) (p : Params) (pass slice : Nat) (h : Ready p pass slice s) :
    WP isa (.block Impl.Argon2.AArch64.FillSlice.setup) s (Prepared s · p pass slice) := by
  refine (SegmentSetup.register_ok s .x24 0 (by decide)).mono ?_
  rintro t ⟨laneWord, keeps⟩
  obtain ⟨lane, header⟩ := h.header
  obtain ⟨old, words⟩ := header.words
  have next : FillHeader.Ready p pass 0 slice t := header.of_state (by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact keeps.regs _ (by decide))
    keeps.sp keeps.mem keeps.rd keeps.wr laneWord ((keeps.regs .x22 (by decide)).trans words.sliceWord)
  exact ⟨next.segment h.parameters, keeps⟩

end VG.Proof.Argon2.AArch64.FillSlice
