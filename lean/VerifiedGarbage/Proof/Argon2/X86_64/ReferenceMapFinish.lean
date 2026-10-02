import VerifiedGarbage.Proof.Argon2.X86_64.ReferenceMapRelative
import VerifiedGarbage.Proof.Argon2.X86_64.Wrap

/-! Wrap the selected relative position into the lane's columns. -/

namespace VG.Proof.Argon2.X86_64.ReferenceMap

open VG VG.X86_64 VG.Impl.Argon2.X86_64.ReferenceMap

structure Result (p : Spec.Argon2.Params) (pass lane slice index : Nat) (s t : State) : Prop where
  selected : t.gpr .r9 = BitVec.ofNat 64 (chosenLane p pass lane slice (s.gpr .rdi))
  column : t.gpr .rdi = BitVec.ofNat 64
    ((windowStart p pass slice + relativeValue p pass lane slice index (s.gpr .rdi)) % p.laneLen)
  original : t.gpr .r11 = s.gpr .rdi
  position : Position p lane slice index t
  keeps : Divide.Keeps changed s t

theorem finish_ok (s a : State) (p : Spec.Argon2.Params) (pass lane slice index : Nat)
    (bounds : Bounds p pass lane slice index) (mapped : Mapped p pass lane slice index s a) :
    WP isa finish a (Result p pass lane slice index s) := by
  unfold finish
  refine WP.seq ((wrapArgs_ok a).mono ?_)
  rintro b ⟨sum, length, kb⟩
  have sumWord : b.gpr .rdi = BitVec.ofNat 64
      (windowStart p pass slice + relativeValue p pass lane slice index (s.gpr .rdi)) := by
    rw [sum, mapped.relative, mapped.start, ← BitVec.ofNat_add, Nat.add_comm]
  have sumBound : windowStart p pass slice + relativeValue p pass lane slice index (s.gpr .rdi)
      < 2 ^ 64 := by
    have small := bounds.sum_bound (s.gpr .rdi)
    have q := bounds.laneLength_bound
    omega
  have sumNat : (b.gpr .rdi).toNat =
      windowStart p pass slice + relativeValue p pass lane slice index (s.gpr .rdi) := by
    rw [sumWord, word_nat _ sumBound]
  have lengthNat : (b.gpr .rsi).toNat = p.laneLen := by
    rw [length, mapped.position.laneLength,
      word_nat _ (Nat.lt_trans bounds.laneLength_bound (by decide))]
  refine (Wrap.code_nat_ok b (by rw [sumNat, lengthNat]; exact bounds.sum_bound _)).mono ?_
  rintro t ⟨out, kt⟩
  have kb' : Divide.Keeps changed a b := kb.mono (by decide)
  have kt' : Divide.Keeps changed b t := kt.mono (by decide)
  refine ⟨?_, ?_, ?_, mapped.position.of_keeps (kb'.trans kt'),
    mapped.keeps.trans (kb'.trans kt')⟩
  · exact (kt.regs .r9 (by decide)).trans ((kb.regs .r9 (by decide)).trans mapped.selected)
  · rw [out, sumNat, lengthNat]
  · exact (kt.regs .r11 (by decide)).trans ((kb.regs .r11 (by decide)).trans mapped.original)

end VG.Proof.Argon2.X86_64.ReferenceMap
