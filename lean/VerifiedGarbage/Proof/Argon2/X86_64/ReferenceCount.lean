import VerifiedGarbage.Impl.Argon2.X86_64.ReferenceCount
import VerifiedGarbage.Proof.Argon2.X86_64.CountCandidates
import VerifiedGarbage.Proof.Argon2.X86_64.CountCandidatesCT
import VerifiedGarbage.Proof.Argon2.X86_64.SelectWindow

/-! The selected reference window, with public pass control only. -/

namespace VG.Proof.Argon2.X86_64.ReferenceCount

open VG VG.X86_64 VG.Impl.Argon2.X86_64.ReferenceCount

theorem code_ok (s : State) : WP isa code s fun t =>
    t.gpr .r8 = (if s.gpr .rdi = s.gpr .rsi then
      CountCandidates.base s + s.gpr .r15 - 1 else
      CountCandidates.base s + Divide.mask (decide ((s.gpr .r15).toNat < 1))) ∧
    Divide.Keeps CountCandidates.changed s t := by
  unfold code
  refine WP.seq ((CountCandidates.code_ok s).mono ?_)
  rintro a ⟨same, other, keeps⟩
  refine (SelectWindow.code_ok a).mono ?_
  rintro t ⟨out, tail⟩
  refine ⟨?_, keeps.trans (tail.mono (by decide))⟩
  rw [out, keeps.regs .rdi (by decide), keeps.regs .rsi (by decide), same, other]

theorem code_rel : RelCT isa (fun s t => s.gpr .r9 = t.gpr .r9) code
    (fun _ _ => True) :=
  CountCandidates.code_rel.seq SelectWindow.code_secret_rel

end VG.Proof.Argon2.X86_64.ReferenceCount
