import VerifiedGarbage.Impl.Argon2.X86_64.ReferenceCount
import VerifiedGarbage.Proof.Argon2.Reference
import VerifiedGarbage.Proof.Framework.Offset
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

theorem same_word (b i : Nat) (positive : 0 < b + i) :
    BitVec.ofNat 64 b + BitVec.ofNat 64 i - (1 : Addr) =
      BitVec.ofNat 64 (b + i - 1) := by
  rw [← BitVec.ofNat_add]
  change BitVec.ofNat 64 (b + i) - BitVec.ofNat 64 1 = _
  exact Offset.ofNat_sub_ofNat (by omega)

theorem other_word (b i : Nat) (bound : i < 2 ^ 64) (positive : i = 0 → 0 < b) :
    BitVec.ofNat 64 b + Divide.mask (decide ((BitVec.ofNat 64 i).toNat < 1)) =
      BitVec.ofNat 64 (b - (if i = 0 then 1 else 0)) := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt bound]
  by_cases zero : i = 0
  · simp only [zero, show decide ((0 : Nat) < 1) = true from rfl, Divide.mask, ite_true]
    rw [BitVec.add_neg_eq_sub]
    change BitVec.ofNat 64 b - BitVec.ofNat 64 1 = _
    exact Offset.ofNat_sub_ofNat (by have := positive zero; omega)
  · have notSmall : ¬i < 1 := by omega
    simp only [notSmall, decide_false, Divide.mask, Bool.false_eq_true, ite_false,
      zero, Nat.sub_zero]
    change BitVec.ofNat 64 b + 0#64 = BitVec.ofNat 64 b
    rw [BitVec.add_zero]

theorem code_rel : RelCT isa (fun s t => s.gpr .r9 = t.gpr .r9) code
    (fun _ _ => True) :=
  CountCandidates.code_rel.seq SelectWindow.code_secret_rel

end VG.Proof.Argon2.X86_64.ReferenceCount
