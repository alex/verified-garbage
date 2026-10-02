import VerifiedGarbage.Proof.Argon2.AArch64.SegmentSetupCheck
import VerifiedGarbage.Proof.Argon2.SegmentStart

/-! Fill one complete segment, including the initialized prefix and empty suffix. -/

namespace VG.Proof.Argon2.AArch64.SegmentSetup

open VG VG.AArch64 VG.Spec.Argon2 VG.Impl.Argon2.AArch64.SegmentSetup

theorem code_ok (s : State) (p : Params) (pass lane slice : Nat)
    (h : Ready p pass lane slice s) (state : FillState)
    (represented : Proof.Argon2.Represents s.mem (FillKernel.matrix s) p.blocks state.memory) :
    WP isa code s (FillSegment.Finished s · p pass lane slice
      (Proof.Argon2.segment p pass lane slice 0 p.segmentLen state)) := by
  rw [Proof.Argon2.segment_start p pass lane slice state h.parameters.segment_bound.1]
  change WP isa code s (FillSegment.Finished s · p pass lane slice
    (Proof.Argon2.segment p pass lane slice (start pass slice) (p.segmentLen - start pass slice) state))
  unfold code
  refine WP.seq ((prepare_ok s p pass lane slice h).mono ?_)
  intro a prepared
  refine WP.seq ((check_prepared_ok prepared).mono ?_)
  rintro b ⟨prepared, flag⟩
  have matrix := prepared.represents h state.memory represented
  refine WP.ite (decide (start pass slice < p.segmentLen)) flag ?_ ?_
  · intro taken
    have bound := of_decide_eq_true taken
    have active := prepared.context.activate bound (start_active pass slice)
    refine (FillSegment.loop_ok (p.segmentLen - start pass slice) b p pass lane slice (start pass slice) 0
      active state matrix (by omega) (by omega)).mono ?_
    intro t finished
    exact finished_prepared prepared finished
  · intro skipped
    have bound := of_decide_eq_false skipped
    have minimum := h.parameters.segment_bound.1
    have last : start pass slice = p.segmentLen := by have := start_le pass slice p.segmentLen minimum; omega
    have finished : FillSegment.Finished b b p pass lane slice state :=
      ⟨matrix, rfl, rfl, last ▸ prepared.context.position, prepared.context.layout,
        ⟨0, prepared.context.cache⟩, prepared.context.matrixWork, prepared.context.cache.words.passWord,
        prepared.context.lanesWord, fun _ _ _ => rfl, rfl, rfl, Frame.refl _ _, rfl⟩
    rw [last, Nat.sub_self, Proof.Argon2.segment_zero]
    exact WP.block_nil (finished_prepared prepared finished)

end VG.Proof.Argon2.AArch64.SegmentSetup
