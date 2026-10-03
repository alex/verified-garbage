import VerifiedGarbage.Proof.TripleDes.X86_64.BitslicedAvx2.SboxLit
import VerifiedGarbage.Proof.Framework.X86_64.StraightY
import VerifiedGarbage.Proof.TripleDes.Bitslice.Io
import VerifiedGarbage.Proof.Framework.Bitslice.Atoms

/-!
# The transposition of the AVX2 state, by evaluation

The 64 state words are the 32-byte slots at `rsi`. The transposition only
moves and XORs bits within the quadword lanes of the words, and masks them
with constants: the lane domain evaluates it on words of atoms (bit `t` of
word `i` is atom `64 i + t`) once, and the check that bit `p` of word `j` is
then atom `64 p + j` proves, through the quadword-lane evaluator, that it
transposes the 64 quadwords of every lane (`transpose_ok`).
-/

namespace VG.Proof.TripleDes.X86_64.BitslicedAvx2

open VG VG.X86_64 VG.X86_64.StraightY VG.Bitslice VG.Impl.TripleDes.X86_64.BitsliceAvx2
open VG.Proof.TripleDes.Bitslice (transposeW)

/-- The state words. -/
def stateCfg : Cfg := { base := .rsi, slots := 64 }

/-- State word `j`. -/
def words (s : State) (j : Nat) : BitVec 256 := s.mem.readW (yAddr (s.gpr .rsi) j) 256

/-- Quadword lane `q` of the state words. -/
def laneW (s : State) (q : Nat) : Nat → BitVec 64 := fun j => qw (words s j) q

def transEnv : Env (Nat × Nat) :=
  { reg := fun _ => none, slot := fun k => if k < 64 then some (inWord k) else none }

def transPost (e : Env (Nat × Nat)) : Bool :=
  (List.range 64).all fun j => e.slot j == some (outWord (fun p => [64 * p + j]))

theorem transpose_check :
    check (lanes 64 12) stateCfg (instrs transposeProg.lit) transEnv transPost = true := by
  decide +kernel

theorem transpose_code : instrs transposeProg.lit = transpose := by
  rw [← transposeProg.lit_eq]; rfl

/-- The state words' area. -/
def stateR (s : State) : Region := ⟨s.gpr .rsi, 2048⟩

theorem transpose_nogpr :
    (instrs transposeProg.lit).all (fun op => op.dst == none || op.dst == some .rbx) = true := by
  decide +kernel

/-- Each quadword lane of the state words, transposed. Only `rbx` (the masks'
constants) and vector registers change, and in memory only the state words. -/
theorem transpose_ok {s : State} (hok : Ok stateCfg s) :
    ∃ s', runBlock isa transpose s = some s' ∧
      (∀ q < 4, ∀ j < 64, laneW s' q j = transposeW (laneW s q) j) ∧
      (∀ r, r ≠ .rbx → s'.gpr r = s.gpr r) ∧ s'.cf = s.cf ∧ s'.zf = s.zf ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ Frame [stateR s] s.mem s'.mem := by
  obtain ⟨e', he, hpost⟩ := of_check _ _ transpose_check
  rw [transpose_code] at he
  have hrel : Rel (fun q => LaneRel 12 (assign (laneW s q) (2 ^ 12))) stateCfg transEnv s := by
    refine ⟨(fun r a h => by cases h), (fun j a hj hsl q hq => ?_), (fun _ _ h => by cases h),
      (fun _ _ h => by cases h)⟩
    simp only [transEnv] at hsl
    split at hsl
    · rename_i hk
      simp only [Option.some.injEq] at hsl
      subst hsl
      exact inWord_rel (laneW s q) (by omega)
    · cases hsl
  obtain ⟨s', hs', p⟩ := run (fun _ _ => lanes_sound) hok hrel he
  have nog := List.all_eq_true.mp transpose_nogpr
  rw [transpose_code] at nog
  refine ⟨s', hs', fun q hq j hj => ?_, fun r hr => p.gpr r ?_, p.cf, p.zf, p.rd, p.wr, p.frame⟩
  · have hpj := List.all_eq_true.mp hpost j (List.mem_range.mpr hj)
    have hs := p.rel.slot j _ (by show j < 64; omega) (beq_iff_eq.mp hpj) q hq
    have bits := outWord_rel (fun q hq a ha => by simp at ha; omega) hs
    apply BitVec.eq_of_getLsbD_eq
    intro b hb
    have hsj : laneW s' q j = qw (s'.mem.readW (yAddr (s'.gpr stateCfg.base) j) 256) q := rfl
    rw [hsj, bits b hb]
    simp only [xorBits_cons, xorBits_nil, Bool.xor_false, transposeW, getLsbD_ofBits, hb,
      decide_true, Bool.true_and]
    exact bitOf_word (laneW s q) b j hj
  · simp only [Bool.not_eq_false, List.all_eq_true, bne_iff_ne, ne_eq]
    intro op hop h
    have := nog op hop
    simp [h, hr] at this

end VG.Proof.TripleDes.X86_64.BitslicedAvx2
