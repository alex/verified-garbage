import VerifiedGarbage.Proof.Argon2.AArch64.FillPointersArgs
import VerifiedGarbage.Proof.Argon2.AArch64.FillColumn
import VerifiedGarbage.Proof.Argon2.AArch64.BlockAddress

/-! Compose the matrix addresses while retaining the enclosing loop position. -/

namespace VG.Proof.Argon2.AArch64.FillPointers

open VG VG.AArch64 VG.Impl.Argon2.AArch64.FillPointers
open VG.Impl.Argon2.AArch64

def address (base lane column q : Addr) : Addr := (lane * q + column) * 1024 + base

def column (s : State) : Addr := s.gpr .x22 * s.gpr .x21 + s.gpr .x23

def predecessor (s : State) : Addr :=
  (if column s = 0 then s.gpr .x20 else column s) - 1

def changed : List Reg := [.x8, .x2, .x3, .x0, .x1, .x6, .x7, .x12, .x13, .x14, .x15]

theorem current_ok (s : State) : WP isa current s fun t =>
    t.gpr .x8 = address (s.gpr .x4) (s.gpr .x24) (s.gpr .x3) (s.gpr .x20) ∧
    Divide.Keeps [.x8, .x2, .x15] s t := by
  unfold current
  refine WP.seq ((currentArgs_ok s).mono ?_)
  rintro a ⟨lane, ka⟩
  refine (BlockAddress.code_ok a).mono ?_
  rintro t ⟨pointer, kt⟩
  refine ⟨?_, (ka.mono (by decide)).trans kt⟩
  rw [pointer, lane, ka.regs .x20 (by decide), ka.regs .x3 (by decide), ka.regs .x4 (by decide), address]

theorem previous_ok (s : State) : WP isa previous s fun t =>
    t.gpr .x6 = s.gpr .x8 ∧
    t.gpr .x8 = address (s.gpr .x4) (s.gpr .x24) (s.gpr .x0) (s.gpr .x20) ∧
    Divide.Keeps [.x8, .x2, .x3, .x6, .x15] s t := by
  unfold previous
  refine WP.seq ((previousArgs_ok s).mono ?_)
  rintro a ⟨saved, col, lane, ka⟩
  refine (BlockAddress.code_ok a).mono ?_
  rintro t ⟨pointer, kt⟩
  refine ⟨(kt.regs .x6 (by decide)).trans saved, ?_,
    (ka.mono (by decide)).trans (kt.mono (by decide))⟩
  rw [pointer, lane, col, ka.regs .x20 (by decide), ka.regs .x4 (by decide), address]

theorem reference_ok (s : State) : WP isa reference s fun t =>
    t.gpr .x7 = s.gpr .x8 ∧
    t.gpr .x8 = address (s.gpr .x4) (s.gpr .x5) (s.gpr .x1) (s.gpr .x20) ∧
    Divide.Keeps [.x8, .x2, .x3, .x7, .x15] s t := by
  unfold reference
  refine WP.seq ((referenceArgs_ok s).mono ?_)
  rintro a ⟨saved, col, lane, ka⟩
  refine (BlockAddress.code_ok a).mono ?_
  rintro t ⟨pointer, kt⟩
  refine ⟨(kt.regs .x7 (by decide)).trans saved, ?_,
    (ka.mono (by decide)).trans (kt.mono (by decide))⟩
  rw [pointer, lane, col, ka.regs .x20 (by decide), ka.regs .x4 (by decide), address]

theorem code_ok (s : State) : WP isa code s fun t =>
    t.gpr .x6 = address (s.gpr .x4) (s.gpr .x24) (column s) (s.gpr .x20) ∧
    t.gpr .x0 = address (s.gpr .x4) (s.gpr .x24) (predecessor s) (s.gpr .x20) ∧
    t.gpr .x1 = address (s.gpr .x4) (s.gpr .x5) (s.gpr .x0) (s.gpr .x20) ∧
    Divide.Keeps changed s t := by
  unfold code
  refine WP.seq ((saveReference_ok s).mono ?_)
  rintro a ⟨refColumn, ka⟩
  refine WP.seq ((FillColumn.code_ok a).mono ?_)
  rintro b ⟨curColumn, prevColumn, kb⟩
  refine WP.seq ((current_ok b).mono ?_)
  rintro c ⟨curPointer, kc⟩
  refine WP.seq ((previous_ok c).mono ?_)
  rintro d ⟨savedCurrent, prevPointer, kd⟩
  refine WP.seq ((reference_ok d).mono ?_)
  rintro e ⟨savedPrevious, refPointer, ke⟩
  refine (finishArgs_ok e).mono ?_
  rintro t ⟨referenceResult, previousResult, kt⟩
  have coords : column a = column s := by
    unfold column
    rw [ka.regs .x22 (by decide), ka.regs .x21 (by decide), ka.regs .x23 (by decide)]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [kt.regs .x6 (by decide), ke.regs .x6 (by decide), savedCurrent, curPointer,
      kb.regs .x4 (by decide), ka.regs .x4 (by decide), kb.regs .x24 (by decide),
      ka.regs .x24 (by decide), kb.regs .x20 (by decide), ka.regs .x20 (by decide), curColumn]
    exact congrArg (fun col => address (s.gpr .x4) (s.gpr .x24) col (s.gpr .x20)) coords
  · rw [previousResult, savedPrevious, prevPointer, kc.regs .x4 (by decide),
      kc.regs .x24 (by decide), kc.regs .x0 (by decide), kc.regs .x20 (by decide),
      kb.regs .x4 (by decide), ka.regs .x4 (by decide), kb.regs .x24 (by decide),
      ka.regs .x24 (by decide), kb.regs .x20 (by decide), ka.regs .x20 (by decide), prevColumn]
    change address _ _ ((if column a = 0 then a.gpr .x20 else column a) - 1) _ = _
    rw [coords, ka.regs .x20 (by decide), predecessor]
  · rw [referenceResult, refPointer, kd.regs .x4 (by decide), kd.regs .x5 (by decide),
      kd.regs .x1 (by decide), kd.regs .x20 (by decide), kc.regs .x4 (by decide),
      kc.regs .x5 (by decide), kc.regs .x1 (by decide), kc.regs .x20 (by decide),
      kb.regs .x4 (by decide), kb.regs .x5 (by decide), kb.regs .x1 (by decide),
      kb.regs .x20 (by decide), ka.regs .x4 (by decide), ka.regs .x5 (by decide),
      ka.regs .x20 (by decide), refColumn]
  · exact (((((ka.mono (by simp [changed])).trans (kb.mono (by simp [changed]))).trans
      (kc.mono (by simp [changed]))).trans (kd.mono (by simp [changed]))).trans
      (ke.mono (by simp [changed]))).trans (kt.mono (by simp [changed]))

end VG.Proof.Argon2.AArch64.FillPointers
