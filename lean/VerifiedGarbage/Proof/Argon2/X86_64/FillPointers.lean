import VerifiedGarbage.Proof.Argon2.X86_64.FillPointersArgs
import VerifiedGarbage.Proof.Argon2.X86_64.FillColumn
import VerifiedGarbage.Proof.Argon2.X86_64.BlockAddress

/-! Compose the matrix addresses while retaining the enclosing loop position. -/

namespace VG.Proof.Argon2.X86_64.FillPointers

open VG VG.X86_64 VG.Impl.Argon2.X86_64.FillPointers

def address (base lane column q : Addr) : Addr := (lane * q + column) * 1024 + base

def column (s : State) : Addr := s.gpr .r14 * s.gpr .r13 + s.gpr .r15

def predecessor (s : State) : Addr :=
  (if column s = 0 then s.gpr .r12 else column s) - 1

def changed : List Reg := [.rax, .rdx, .rcx, .rdi, .rsi, .r10, .r11]

theorem current_ok (s : State) : WP isa current s fun t =>
    t.gpr .rax = address (s.gpr .r8) (s.gpr .rbx) (s.gpr .rcx) (s.gpr .r12) ∧
    Divide.Keeps [.rax, .rdx] s t := by
  unfold current
  refine WP.seq ((currentArgs_ok s).mono ?_)
  rintro a ⟨lane, ka⟩
  refine (BlockAddress.code_ok a).mono ?_
  rintro t ⟨pointer, kt⟩
  refine ⟨?_, (ka.mono (by simp)).trans kt⟩
  rw [pointer, lane, ka.regs .r12 (by decide), ka.regs .rcx (by decide), ka.regs .r8 (by decide), address]

theorem previous_ok (s : State) : WP isa previous s fun t =>
    t.gpr .r10 = s.gpr .rax ∧
    t.gpr .rax = address (s.gpr .r8) (s.gpr .rbx) (s.gpr .rdi) (s.gpr .r12) ∧
    Divide.Keeps [.rax, .rdx, .rcx, .r10] s t := by
  unfold previous
  refine WP.seq ((previousArgs_ok s).mono ?_)
  rintro a ⟨saved, col, lane, ka⟩
  refine (BlockAddress.code_ok a).mono ?_
  rintro t ⟨pointer, kt⟩
  refine ⟨(kt.regs .r10 (by decide)).trans saved, ?_,
    (ka.mono (by simp)).trans (kt.mono (by simp))⟩
  rw [pointer, lane, col, ka.regs .r12 (by decide), ka.regs .r8 (by decide), address]

theorem reference_ok (s : State) : WP isa reference s fun t =>
    t.gpr .r11 = s.gpr .rax ∧
    t.gpr .rax = address (s.gpr .r8) (s.gpr .r9) (s.gpr .rsi) (s.gpr .r12) ∧
    Divide.Keeps [.rax, .rdx, .rcx, .r11] s t := by
  unfold reference
  refine WP.seq ((referenceArgs_ok s).mono ?_)
  rintro a ⟨saved, col, lane, ka⟩
  refine (BlockAddress.code_ok a).mono ?_
  rintro t ⟨pointer, kt⟩
  refine ⟨(kt.regs .r11 (by decide)).trans saved, ?_,
    (ka.mono (by simp)).trans (kt.mono (by simp))⟩
  rw [pointer, lane, col, ka.regs .r12 (by decide), ka.regs .r8 (by decide), address]

theorem code_ok (s : State) : WP isa code s fun t =>
    t.gpr .r10 = address (s.gpr .r8) (s.gpr .rbx) (column s) (s.gpr .r12) ∧
    t.gpr .rdi = address (s.gpr .r8) (s.gpr .rbx) (predecessor s) (s.gpr .r12) ∧
    t.gpr .rsi = address (s.gpr .r8) (s.gpr .r9) (s.gpr .rdi) (s.gpr .r12) ∧
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
    rw [ka.regs .r14 (by decide), ka.regs .r13 (by decide), ka.regs .r15 (by decide)]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [kt.regs .r10 (by decide), ke.regs .r10 (by decide), savedCurrent, curPointer,
      kb.regs .r8 (by decide), ka.regs .r8 (by decide), kb.regs .rbx (by decide),
      ka.regs .rbx (by decide), kb.regs .r12 (by decide), ka.regs .r12 (by decide), curColumn]
    exact congrArg (fun col => address (s.gpr .r8) (s.gpr .rbx) col (s.gpr .r12)) coords
  · rw [previousResult, savedPrevious, prevPointer, kc.regs .r8 (by decide),
      kc.regs .rbx (by decide), kc.regs .rdi (by decide), kc.regs .r12 (by decide),
      kb.regs .r8 (by decide), ka.regs .r8 (by decide), kb.regs .rbx (by decide),
      ka.regs .rbx (by decide), kb.regs .r12 (by decide), ka.regs .r12 (by decide), prevColumn]
    change address _ _ ((if column a = 0 then a.gpr .r12 else column a) - 1) _ = _
    rw [coords, ka.regs .r12 (by decide), predecessor]
  · rw [referenceResult, refPointer, kd.regs .r8 (by decide), kd.regs .r9 (by decide),
      kd.regs .rsi (by decide), kd.regs .r12 (by decide), kc.regs .r8 (by decide),
      kc.regs .r9 (by decide), kc.regs .rsi (by decide), kc.regs .r12 (by decide),
      kb.regs .r8 (by decide), kb.regs .r9 (by decide), kb.regs .rsi (by decide),
      kb.regs .r12 (by decide), ka.regs .r8 (by decide), ka.regs .r9 (by decide),
      ka.regs .r12 (by decide), refColumn]
  · exact (((((ka.mono (by simp [changed])).trans (kb.mono (by simp [changed]))).trans
      (kc.mono (by simp [changed]))).trans (kd.mono (by simp [changed]))).trans
      (ke.mono (by simp [changed]))).trans (kt.mono (by simp [changed]))

end VG.Proof.Argon2.X86_64.FillPointers
