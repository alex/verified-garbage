import VerifiedGarbage.Proof.Argon2.X86_64.ReferenceMapWindow
import VerifiedGarbage.Proof.Argon2.X86_64.Relative
import VerifiedGarbage.Proof.Framework.X86_64.Abi

/-! Apply the squared J₁ mapping while retaining the lane and window start. -/

namespace VG.Proof.Argon2.X86_64.ReferenceMap

open VG VG.X86_64 VG.Impl.Argon2.X86_64.ReferenceMap

theorem relativeWord_ok (s : State) (positive : 0 < (s.gpr .rsi).toNat)
    (bound : (s.gpr .rsi).toNat < 2 ^ 32) :
    WP isa VG.Impl.Argon2.X86_64.Relative.code s fun t =>
      t.gpr .rax = BitVec.ofNat 64
        ((s.gpr .rsi).toNat - 1 - (s.gpr .rsi).toNat *
          ((s.gpr .rdi &&& 0xffffffff).toNat * (s.gpr .rdi &&& 0xffffffff).toNat / 2 ^ 32) /
          2 ^ 32) ∧ Divide.Keeps [.rax, .rdx, .rcx] s t := by
  refine WP.mono_mx (by decide +kernel) (Relative.code_nat_ok s positive bound) ?_
  rintro t ⟨out, other, mem, rd, wr⟩ mx
  refine ⟨out, ⟨?_, mem, rd, wr, mx⟩⟩
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  exact other r hr.1 hr.2.1 hr.2.2

structure Mapped (p : Spec.Argon2.Params) (pass lane slice index : Nat) (s t : State) : Prop where
  selected : t.gpr .r9 = BitVec.ofNat 64 (chosenLane p pass lane slice (s.gpr .rdi))
  relative : t.gpr .rax = BitVec.ofNat 64 (relativeValue p pass lane slice index (s.gpr .rdi))
  start : t.gpr .r10 = BitVec.ofNat 64 (windowStart p pass slice)
  original : t.gpr .r11 = s.gpr .rdi
  position : Position p lane slice index t
  keeps : Divide.Keeps changed s t

theorem relative_ok (s a : State) (p : Spec.Argon2.Params) (pass lane slice index : Nat)
    (bounds : Bounds p pass lane slice index) (counted : Counted p pass lane slice index s a) :
    WP isa relative a (Mapped p pass lane slice index s) := by
  unfold relative
  refine WP.seq ((relativeArgs_ok a).mono ?_)
  rintro b ⟨selected, random, count, kb⟩
  have countNat : (b.gpr .rsi).toNat = windowSize p pass lane slice index (s.gpr .rdi) := by
    rw [count, counted.count, word_nat _ (Nat.lt_trans (bounds.windowSize_bound32 _) (by decide))]
  have randomWord : b.gpr .rdi = s.gpr .rdi := random.trans counted.original
  refine (relativeWord_ok b
    (by rw [countNat]; exact bounds.windowSize_positive _)
    (by rw [countNat]; exact bounds.windowSize_bound32 _)).mono ?_
  rintro t ⟨out, kt⟩
  have kb' : Divide.Keeps changed a b := kb.mono (by decide)
  have kt' : Divide.Keeps changed b t := kt.mono (by decide)
  refine ⟨?_, ?_, ?_, ?_, counted.position.of_keeps (kb'.trans kt'),
    counted.keeps.trans (kb'.trans kt')⟩
  · exact (kt.regs .r9 (by decide)).trans (selected.trans counted.selected)
  · simpa only [relativeValue, countNat, randomWord] using out
  · exact (kt.regs .r10 (by decide)).trans ((kb.regs .r10 (by decide)).trans counted.start)
  · exact (kt.regs .r11 (by decide)).trans ((kb.regs .r11 (by decide)).trans counted.original)

end VG.Proof.Argon2.X86_64.ReferenceMap
