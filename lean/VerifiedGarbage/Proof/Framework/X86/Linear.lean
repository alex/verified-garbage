import VerifiedGarbage.Proof.Framework.X86.Straight
import VerifiedGarbage.Proof.Framework.Bitslice.Atoms

/-!
# x86 (32-bit): linear layers of bitsliced code, by evaluation

Untrusted: everything here is checked by Lean.

As on x86-64 (`Framework/X86_64/Linear.lean`), but with the words of the
state in slots: straight-line code that only moves and XORs bits of 32-bit
words, and masks them with constants, is checked by evaluating it
(`Straight.check`) over the lane domain (`Bitslice.lanes`), on input words
given as atoms: bit `t` of input word `i` is atom `32 i + t`. The inputs
are slots (`ins`: slot `j` holds input word `i`) and the external words
`[ext + 4j]`, input words `xb + j`. `linPost` compares each output slot with
the XOR of the atoms `g p` at each bit position `p`, and `linear_ok` turns a
successful check into a statement about the machine: bit `p` of the output
slot is the XOR of the input bits `g p`.
-/

namespace VG.X86.Straight

open VG.Bitslice

/-- The slots `ins` hold input words. -/
def linEnv (ins : List (Nat × Nat)) : Env (Nat × Nat) :=
  { reg := fun _ => none, slot := fun j => (ins.find? (·.1 == j)).map (inWordW 32 ·.2) }

/-- External word `j` is input word `xb + j`. -/
def linExt (xb j : Nat) : Option (Nat × Nat) := some (inWordW 32 (xb + j))

/-- Each output slot `j` (of the `n` slots) holds `outWordW 32 g`, with atoms below `2 ^ k`. -/
def linPost (n k : Nat) (outs : List (Nat × (Nat → List Nat))) (e : Env (Nat × Nat)) : Bool :=
  outs.all fun o => decide (o.1 < n) && e.slot o.1 == some (outWordW 32 o.2) &&
    (List.range 32).all fun p => (o.2 p).all (· < 2 ^ k)

/-- A linear block that the evaluator accepts, on the machine. -/
theorem linear_ok {k xb : Nat} {c : Cfg} {is : List Instr} {ins : List (Nat × Nat)}
    {outs : List (Nat × (Nat → List Nat))}
    (hchk : check (lanes 32 k) c (linExt xb) is (linEnv ins) (linPost c.slots k outs) = true)
    {s : State} (hok : Ok c s) (W : Nat → BitVec 32)
    (hin : ∀ j i, (j, i) ∈ ins → j < c.slots → 32 * i + 32 ≤ 2 ^ k ∧
      W i = s.mem.readW (wordAddr (s.gpr c.base) j) 32)
    (hext : ∀ j < c.exts,
      32 * (xb + j) + 32 ≤ 2 ^ k ∧ W (xb + j) = s.mem.readW (wordAddr (s.gpr c.ext) j) 32) :
    ∃ s', runBlock isa is s = some s' ∧
      (∀ j g, (j, g) ∈ outs → ∀ p < 32,
        (s'.mem.readW (wordAddr (s.gpr c.base) j) 32).getLsbD p = xorBits W (g p)) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r, (is.all fun i => i.dst != some r) = true → s'.gpr r = s.gpr r) ∧
      Frame [slotRegion c s] s.mem s'.mem := by
  obtain ⟨e', he, hpost⟩ := of_check _ _ _ hchk
  have hrel : Rel (LaneRel k (assign W (2 ^ k))) c (linExt xb) (linEnv ins) s := by
    refine ⟨(fun r a h => by cases h), fun j a hj h => ?_, fun j a hj h => ?_⟩
    · simp only [linEnv, Option.map_eq_some_iff] at h
      obtain ⟨⟨j', i⟩, hf, rfl⟩ := h
      have hj' : j' = j := by simpa using List.find?_some hf
      subst hj'
      obtain ⟨h1, h2⟩ := hin j' i (List.mem_of_find?_eq_some hf) hj
      rw [← h2]; exact inWordW_rel W h1
    · simp only [linExt, Option.some.injEq] at h; subst h
      obtain ⟨h1, h2⟩ := hext j hj
      rw [← h2]; exact inWordW_rel W h1
  obtain ⟨s', hs', p⟩ := run lanes_sound hok hrel he
  refine ⟨s', hs', fun j g hjg q hq => ?_, p.rd, p.wr, fun r hr => p.other r (by simp [hr]), p.frame⟩
  have h := List.all_eq_true.mp hpost (j, g) hjg
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, List.all_eq_true, List.mem_range]
    at h
  have := p.rel.slot j _ h.1.1 h.1.2
  rw [p.base] at this
  exact outWordW_rel (fun p hp a ha => h.2 p hp a ha) this q hq

end VG.X86.Straight
