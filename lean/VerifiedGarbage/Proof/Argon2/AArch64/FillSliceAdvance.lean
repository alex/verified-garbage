import VerifiedGarbage.Impl.Argon2.AArch64.FillSlices
import VerifiedGarbage.Proof.Argon2.AArch64.FillSlice

/-! Slice advancement retains the public header and matrix allocation. -/

namespace VG.Proof.Argon2.AArch64.FillSlices

open VG VG.AArch64 VG.Spec.Argon2 VG.Impl.Argon2.AArch64.FillSlices

theorem advance_ok (s : State) (ha : (s.gpr .x22 + 1).toNat < 2 ^ 63) :
    WP isa (.block advance) s fun t => t.gpr .x22 = s.gpr .x22 + 1 ∧
      eval (.nonzero .x .x14) t = some (decide ((s.gpr .x22 + 1).toNat < 4)) ∧
      Divide.Keeps [.x22, .x12, .x13, .x14, .x15] s t := by
  simp only [advance, List.flatten_cons, List.flatten_nil, List.append_nil,
    Impl.Argon2.AArch64.Instructions.comparei]
  apply WP.block_append
  refine (Instructions.addi_ok s .x22 1 (by decide) (by decide) (by decide)).mono ?_
  rintro a ⟨value, ka⟩
  apply WP.block_append
  refine (SegmentSetup.register_ok a .x13 4 (by decide)).mono ?_
  rintro b ⟨bound, kb⟩
  have left : (b.gpr .x22).toNat < 2 ^ 63 := by
    rw [kb.regs .x22 (by decide), value]; exact ha
  have right : (b.gpr .x13).toNat < 2 ^ 63 := by rw [bound]; decide
  refine (Instructions.compare_ok b .x22 .x13 left right).mono ?_
  rintro t ⟨flag, kt⟩
  have val := (kt.regs .x22 (by decide)).trans ((kb.regs .x22 (by decide)).trans value)
  refine ⟨val, ?_, (ka.mono (by decide)).trans
    ((kb.mono (by decide)).trans (kt.mono (by decide)))⟩
  simp only [eval, State.read, Size.bits, BitVec.setWidth_eq, flag,
    kb.regs .x22 (by decide), value, bound, show (BitVec.ofNat 64 4).toNat = 4 from rfl]
  cases decide ((s.gpr .x22 + 1).toNat < 4) <;> rfl

theorem advanced_header {s t : State} {p : Params} {pass lane slice : Nat}
    (h : FillHeader.Ready p pass lane slice s) (k : Divide.Keeps [.x22, .x12, .x13, .x14, .x15] s t)
    (value : t.gpr .x22 = BitVec.ofNat 64 (slice + 1)) : FillHeader.Ready p pass lane (slice + 1) t := by
  obtain ⟨old, words⟩ := h.words
  exact h.of_state (by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact k.regs _ (by decide))
    k.sp k.mem k.rd k.wr ((k.regs .x24 (by decide)).trans words.laneWord) value

end VG.Proof.Argon2.AArch64.FillSlices
