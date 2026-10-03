import VerifiedGarbage.Proof.TripleDes.X86_64.Bitsliced.Machine
import VerifiedGarbage.Proof.TripleDes.Bitslice.Io
import VerifiedGarbage.Proof.Framework.Bitslice.Atoms

/-!
# The transposition of the state, by evaluation

The transposition only moves and XORs bits of the 64 state words (slots
0–63), and masks them with constants: the lane domain evaluates it on
words of atoms (bit `t` of word `i` is atom `64 i + t`), and the check
that bit `p` of word `j` is then atom `64 p + j` proves that it transposes
any 64 words (`transpose_ok`).
-/

namespace VG.Proof.TripleDes.X86_64.Bitsliced

open VG VG.X86_64 VG.X86_64.Straight VG.Bitslice VG.Impl.TripleDes.X86_64.Bitslice
open VG.Proof.TripleDes.Bitslice (transposeW)

/-- The spill slots and the state words. -/
def stateCfg : Cfg := { base := .rcx, slots := 72, ext := .rsp, exts := 0 }

def transEnv : Env (Nat × Nat) :=
  { reg := fun _ => none, slot := fun k => if 8 ≤ k ∧ k < 72 then some (inWord (k - 8)) else none }

def transPost (e : Env (Nat × Nat)) : Bool :=
  (List.range 64).all fun j => e.slot (stSlot j) == some (outWord (fun p => [64 * p + j]))

theorem transpose_check :
    check (lanes 64 12) stateCfg (fun _ => none) (instrs transposeProg.lit) transEnv transPost = true := by
  decide +kernel

theorem transpose_code : instrs transposeProg.lit = transpose := by
  rw [← transposeProg.lit_eq]; rfl

/-- The spill slots and the state words (slots 0–71). -/
def stateR (s : State) : Region := ⟨s.gpr .rcx, 576⟩

theorem transpose_ok {s : State} (h : Room s) :
    ∃ s', runBlock isa transpose s = some s' ∧ (∀ j < 64, words s' j = transposeW (words s) j) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.gpr .rcx = s.gpr .rcx ∧ s'.gpr .rsp = s.gpr .rsp ∧
      Frame [stateR s] s.mem s'.mem := by
  obtain ⟨e', he, hpost⟩ := of_check _ _ _ transpose_check
  rw [transpose_code] at he
  have hok : Ok stateCfg s :=
    Ok.of_region h.scratch rfl (by show 8 * 72 ≤ 1024; decide) (by decide) rfl
  have hrel : Rel (LaneRel 12 (assign (words s) (2 ^ 12))) stateCfg (fun _ => none) transEnv s := by
    refine ⟨(fun r a h => by cases h), (fun j a hj hsl => ?_), (fun _ _ hj => ?_)⟩
    swap
    · exact absurd hj (by simp [stateCfg])
    simp only [transEnv] at hsl
    split at hsl
    · rename_i hk
      simp only [Option.some.injEq] at hsl
      subst hsl
      have e : sl s j = words s (j - 8) := by
        simp only [words, stSlot]; rw [show 8 + (j - 8) = j by omega]
      show LaneRel 12 _ _ (s.mem.readW (wordAddr (s.gpr .rcx) j) 64)
      rw [show s.mem.readW (wordAddr (s.gpr .rcx) j) 64 = sl s j from rfl, e]
      exact inWord_rel (words s) (by omega)
    · cases hsl
  obtain ⟨s', hs', p⟩ := run lanes_sound hok hrel he
  refine ⟨s', hs', fun j hj => ?_, p.rd, p.wr, p.base, p.ext, p.frame⟩
  have hpj := List.all_eq_true.mp hpost j (List.mem_range.mpr hj)
  have hs := p.rel.slot (stSlot j) _ (by unfold stSlot; show 8 + j < 72; omega) (beq_iff_eq.mp hpj)
  have bits := outWord_rel (fun q hq a ha => by simp at ha; omega) hs
  apply BitVec.eq_of_getLsbD_eq
  intro b hb
  have hsj : words s' j = s'.mem.readW (wordAddr (s'.gpr stateCfg.base) (stSlot j)) 64 := rfl
  rw [hsj, bits b hb]
  simp only [xorBits_cons, xorBits_nil, Bool.xor_false, transposeW, getLsbD_ofBits, hb,
    decide_true, Bool.true_and]
  exact bitOf_word (words s) b j hj

end VG.Proof.TripleDes.X86_64.Bitsliced
