import VerifiedGarbage.Proof.Framework.Arm.Straight
import VerifiedGarbage.Proof.Framework.Bitslice.Lanes
import VerifiedGarbage.Proof.Framework.Bitslice.Table

/-!
# ARMv7: linear layers of bitsliced code, by evaluation

Untrusted: everything here is checked by Lean.

As `Framework/AArch64/Linear.lean`, on 32-bit words: straight-line code
that only moves and XORs bits of words, and masks them with constants, is
checked by evaluating it (`Straight.check`) over the lane domain
(`Bitslice.lanes`), on input words given as atoms: bit `t` of input word
`i` is atom `32 i + t`. The inputs are registers (`ins`) and the external
words `[ext, #4j]`, input words `xb + j`. `linPost` compares each output
register with the XOR of the atoms `g p` at each bit position `p`, and
`linear_ok` turns a successful check into a statement about the machine:
bit `p` of the output register is the XOR of the input bits `g p`.
-/

namespace VG.Arm.Straight

open VG.Bitslice

/-! ## Words of atoms (as `Framework/Bitslice/Atoms.lean`, for 32-bit words) -/

/-- Input word `i`: bit `t` is atom `32 i + t`. -/
def inWord (i : Nat) : Nat × Nat := (0, mk 32 (fun t => [32 * i + t]) 32)

/-- The word whose bit `p` is the XOR of the atoms `g p`. -/
def outWord (g : Nat → List Nat) : Nat × Nat := (0, mk 32 g 32)

/-- Bit `a % 32` of word `a / 32`. -/
def bitOf (W : Nat → BitVec 32) (a : Nat) : Bool := (W (a / 32)).getLsbD (a % 32)

/-- The XOR of the bits `l` of the words `W`. -/
def xorBits (W : Nat → BitVec 32) (l : List Nat) : Bool := l.foldr (fun a b => bitOf W a ^^ b) false

@[simp] theorem xorBits_nil (W : Nat → BitVec 32) : xorBits W [] = false := rfl

@[simp] theorem xorBits_cons (W : Nat → BitVec 32) (a : Nat) (l : List Nat) :
    xorBits W (a :: l) = (bitOf W a ^^ xorBits W l) := rfl

theorem bitOf_word (W : Nat → BitVec 32) (i t : Nat) (ht : t < 32) :
    bitOf W (32 * i + t) = (W i).getLsbD t := by
  simp only [bitOf]
  rw [Nat.mul_add_div (by decide), Nat.div_eq_of_lt ht, Nat.add_zero, Nat.mul_add_mod,
    Nat.mod_eq_of_lt ht]

/-- The assignment of the atoms below `N` given by the words `W`. -/
def assign (W : Nat → BitVec 32) (N : Nat) : Nat := tableOf (bitOf W) N

theorem xorA_assign (W : Nat → BitVec 32) {N : Nat} {l : List Nat} (hl : ∀ a ∈ l, a < N) :
    xorA (assign W N) l = xorBits W l := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [xorA, List.foldr_cons, xorBits_cons] at ih ⊢
    rw [ih fun b hb => hl b (by simp [hb]), assign, testBit_tableOf]
    simp [hl a (by simp)]

theorem inWord_rel {k : Nat} (W : Nat → BitVec 32) {i : Nat} (hi : 32 * i + 32 ≤ 2 ^ k) :
    LaneRel k (assign W (2 ^ k)) (inWord i) (W i) := by
  refine ⟨Nat.two_pow_pos _, fun q hq => ?_⟩
  simp only [inWord, Nat.zero_testBit, Bool.false_xor]
  rw [par_mk hq (Nat.le_refl _) _ (fun q' hq' a ha => by simp at ha; omega), xorA_assign W
    (by intro a ha; simp at ha; omega)]
  simp [hq, bitOf_word W i q hq]

theorem outWord_rel {k : Nat} {W : Nat → BitVec 32} {g : Nat → List Nat} {x : BitVec 32}
    (hg : ∀ p < 32, ∀ a ∈ g p, a < 2 ^ k) (h : LaneRel k (assign W (2 ^ k)) (outWord g) x) :
    ∀ p < 32, x.getLsbD p = xorBits W (g p) := by
  intro p hp
  rw [h.2 p hp]
  simp only [outWord, Nat.zero_testBit, Bool.false_xor]
  rw [par_mk hp (Nat.le_refl _) _ (fun q hq => hg q hq), xorA_assign W (hg p hp)]
  simp [hp]

/-! ## The check -/

/-- The registers `ins` hold input words. -/
def linEnv (ins : List (Reg × Nat)) : Env (Nat × Nat) :=
  { reg := fun r => (ins.find? (·.1 == r)).map (inWord ·.2), slot := fun _ => none }

/-- External word `j` is input word `xb + j`. -/
def linExt (xb j : Nat) : Option (Nat × Nat) := some (inWord (xb + j))

/-- Each output register `r` holds `outWord g`, with atoms below `2 ^ k`. -/
def linPost (k : Nat) (outs : List (Reg × (Nat → List Nat))) (e : Env (Nat × Nat)) : Bool :=
  outs.all fun o => e.reg o.1 == some (outWord o.2) && (List.range 32).all fun p => (o.2 p).all (· < 2 ^ k)

/-- A linear block that the evaluator accepts, on the machine. -/
theorem linear_ok {k xb : Nat} {c : Cfg} {is : List Instr} {ins : List (Reg × Nat)}
    {outs : List (Reg × (Nat → List Nat))}
    (hchk : check (lanes 32 k) c (linExt xb) is (linEnv ins) (linPost k outs) = true)
    {s : State} (hok : Ok c s) (W : Nat → BitVec 32)
    (hin : ∀ r i, (r, i) ∈ ins → 32 * i + 32 ≤ 2 ^ k ∧ W i = s.gpr r)
    (hext : ∀ j < c.exts,
      32 * (xb + j) + 32 ≤ 2 ^ k ∧ W (xb + j) = s.mem.readW (wordAddr (s.gpr c.ext) j) 32) :
    ∃ s', runBlock isa is s = some s' ∧
      (∀ r g, (r, g) ∈ outs → ∀ p < 32, (s'.gpr r).getLsbD p = xorBits W (g p)) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
      (∀ r, (is.all fun i => dstOf i != some r) = true → s'.gpr r = s.gpr r) ∧
      Frame [slotRegion c s] s.mem s'.mem := by
  obtain ⟨e', he, hpost⟩ := of_check _ _ _ hchk
  have hrel : Rel (LaneRel k (assign W (2 ^ k))) c (linExt xb) (linEnv ins) s := by
    refine ⟨fun r a h => ?_, (fun _ _ _ h => by cases h), fun j a hj h => ?_, fun _ _ h => by cases h⟩
    · simp only [linEnv, Option.map_eq_some_iff] at h
      obtain ⟨⟨r', i⟩, hf, rfl⟩ := h
      have hr : r' = r := by simpa using List.find?_some hf
      subst hr
      obtain ⟨h1, h2⟩ := hin r' i (List.mem_of_find?_eq_some hf)
      rw [← h2]; exact inWord_rel W h1
    · simp only [linExt, Option.some.injEq] at h; subst h
      obtain ⟨h1, h2⟩ := hext j hj
      rw [← h2]; exact inWord_rel W h1
  obtain ⟨s', hs', p⟩ := run lanes_sound hok hrel he
  refine ⟨s', hs', fun r g hrg q hq => ?_, p.rd, p.wr, p.sp, fun r hr => p.other r (by simp [hr]), p.frame⟩
  have h := List.all_eq_true.mp hpost (r, g) hrg
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range, decide_eq_true_eq] at h
  exact outWord_rel (fun p hp a ha => h.2 p hp a ha) (p.rel.reg r _ h.1) q hq

end VG.Arm.Straight
