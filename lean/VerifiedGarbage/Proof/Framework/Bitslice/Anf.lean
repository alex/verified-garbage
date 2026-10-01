import VerifiedGarbage.Proof.Framework.Bitslice.Lanes

/-!
# The ANF domain: XORs of ANDs of XORs of rotated words

Untrusted: everything here is checked by Lean.

Code that combines 64-bit words with XOR, AND, OR, NOT (an XOR with
all-ones) and rotations, such as a round of Keccak-f, computes from its
input words (*atoms*, numbered from 0) values that are polynomials over
`GF(2)` (algebraic normal forms) in *linear forms*: XORs of rotated atoms.
An abstract word (`Poly`) is such a polynomial:

* a linear form `lin`, a list of *keys*: key `64 a + r` is atom `a` rotated
  right by `r`;
* a constant `c`: all-ones if set;
* nonlinear monomials `nl`, each the AND of two or more linear forms (with
  no constant).

The operations keep keys, linear forms and monomials sorted and without
duplicates, so that two programs that compute the same polynomial in the
same linear forms get the same `Poly`, which a `decide` compares. That is
only needed for the comparison to succeed: what the evaluation computes is
right however the lists are ordered (`anf_sound`), as the abstract values
are related to concrete words by `eval` alone.

Rotations act on the keys; they keep the lists sorted as long as no
linear form has two keys of the same atom.
-/

namespace VG.Bitslice.Anf

abbrev W := BitVec 64

/-! ## Words -/

/-- All ones. -/
def ones : W := BitVec.allOnes 64

/-- The constant `c`: all ones or zero. -/
def cst (c : Bool) : W := if c then ones else 0

/-- Key `k`: atom `k / 64` rotated right by `k % 64`. -/
def key (V : Nat → W) (k : Nat) : W := (V (k / 64)).rotateRight (k % 64)

/-- A linear form: the XOR of its keys. -/
def lin (V : Nat → W) (l : List Nat) : W := l.foldr (fun k acc => key V k ^^^ acc) 0

/-- A monomial: the AND of its linear forms. -/
def mono (V : Nat → W) (m : List (List Nat)) : W := m.foldr (fun a acc => lin V a &&& acc) ones

/-- The XOR of monomials. -/
def monos (V : Nat → W) (ns : List (List (List Nat))) : W := ns.foldr (fun m acc => mono V m ^^^ acc) 0

structure Poly where
  lin : List Nat
  c : Bool
  nl : List (List (List Nat))
  deriving DecidableEq, Repr

def eval (V : Nat → W) (p : Poly) : W :=
  lin V p.lin ^^^ cst p.c ^^^ monos V p.nl

/-! ## Operations -/

/-- XOR key `k` into the sorted linear form `l`. -/
def keyIns (k : Nat) : List Nat → List Nat
  | [] => [k]
  | j :: l => if k = j then l else if k < j then k :: j :: l else j :: keyIns k l

def linXor (a b : List Nat) : List Nat := a.foldr keyIns b

/-- Rotate each key right by `n`. -/
def linRor (n : Nat) (l : List Nat) : List Nat := l.map fun k => k / 64 * 64 + (k % 64 + n) % 64

/-- Lexicographic order of linear forms. -/
def linCmp : List Nat → List Nat → Ordering
  | [], [] => .eq
  | [], _ :: _ => .lt
  | _ :: _, [] => .gt
  | a :: l, b :: m => if a < b then .lt else if b < a then .gt else linCmp l m

/-- AND the linear form `a` into the sorted monomial `m`. -/
def atomIns (a : List Nat) : List (List Nat) → List (List Nat)
  | [] => [a]
  | b :: m => match linCmp a b with
    | .eq => b :: m
    | .lt => a :: b :: m
    | .gt => b :: atomIns a m

def monoMul (m₁ m₂ : List (List Nat)) : List (List Nat) := m₁.foldr atomIns m₂

/-- Lexicographic order of monomials. -/
def monoCmp : List (List Nat) → List (List Nat) → Ordering
  | [], [] => .eq
  | [], _ :: _ => .lt
  | _ :: _, [] => .gt
  | a :: l, b :: m => match linCmp a b with
    | .eq => monoCmp l m
    | o => o

/-- XOR the monomial `m` into the sorted list `ns`. -/
def monoIns (m : List (List Nat)) : List (List (List Nat)) → List (List (List Nat))
  | [] => [m]
  | n :: ns => match monoCmp m n with
    | .eq => ns
    | .lt => m :: n :: ns
    | .gt => n :: monoIns m ns

def monosXor (a b : List (List (List Nat))) : List (List (List Nat)) := a.foldr monoIns b

def zero : Poly := ⟨[], false, []⟩
def one : Poly := ⟨[], true, []⟩
/-- Atom `a`. -/
def atom (a : Nat) : Poly := ⟨[64 * a], false, []⟩

def pxor (p q : Poly) : Poly := ⟨linXor p.lin q.lin, p.c ^^ q.c, monosXor p.nl q.nl⟩

def pror (n : Nat) (p : Poly) : Poly := ⟨linRor n p.lin, p.c, p.nl.map (·.map (linRor n))⟩

/-- The monomials of `p`, the constant as the empty one and the linear form
as a monomial of one linear form. -/
def terms (p : Poly) : List (List (List Nat)) :=
  (if p.c then [[]] else []) ++ ((if p.lin.isEmpty then [] else [[p.lin]]) ++ p.nl)

def addMono (m : List (List Nat)) (p : Poly) : Poly :=
  match m with
  | [] => ⟨p.lin, !p.c, p.nl⟩
  | [a] => ⟨linXor a p.lin, p.c, p.nl⟩
  | _ => ⟨p.lin, p.c, monoIns m p.nl⟩

def ofMonos (ms : List (List (List Nat))) : Poly := ms.foldr addMono zero

def pand (p q : Poly) : Poly := ofMonos ((terms p).flatMap fun t => (terms q).map fun u => monoMul t u)

def por (p q : Poly) : Poly := pxor (pxor p q) (pand p q)

/-- The ANF domain. -/
def anf : Dom Poly 64 where
  xor a b := some (pxor a b)
  and a b := some (pand a b)
  or a b := some (por a b)
  ror n a := some (pror n a)
  shr _ _ := none
  const v := if v = 0 then some zero else if v = BitVec.allOnes 64 then some one else none

/-! ## Soundness -/

section
variable (V : Nat → W)

theorem rotateRight_xor (x y : W) (n : Nat) :
    (x ^^^ y).rotateRight n = x.rotateRight n ^^^ y.rotateRight n := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [getLsbD_rotateRight_lt _ _ _ hi, BitVec.getLsbD_xor]

theorem rotateRight_and (x y : W) (n : Nat) :
    (x &&& y).rotateRight n = x.rotateRight n &&& y.rotateRight n := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [getLsbD_rotateRight_lt _ _ _ hi, BitVec.getLsbD_and]

theorem rotateRight_zero' (n : Nat) : (0#64).rotateRight n = 0#64 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp [getLsbD_rotateRight_lt _ _ _ hi]

theorem ones_ror (n : Nat) : ones.rotateRight n = ones := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [ones, getLsbD_rotateRight_lt _ _ _ hi, BitVec.getLsbD_allOnes]
  simp [Nat.mod_lt _ (by decide : 0 < 64), hi]

theorem xor_zero' (x : W) : x ^^^ 0 = x := by simp
theorem and_zero' (x : W) : x &&& 0 = 0 := by simp
theorem zero_and' (x : W) : 0 &&& x = 0 := by simp
theorem zero_xor' (x : W) : 0 ^^^ x = x := by simp

theorem and_xor_left (x y z : W) : x &&& (y ^^^ z) = (x &&& y) ^^^ (x &&& z) := by
  apply BitVec.eq_of_getLsbD_eq; intro i _
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_xor]
  cases x.getLsbD i <;> cases y.getLsbD i <;> cases z.getLsbD i <;> rfl

theorem and_xor_right (x y z : W) : (x ^^^ y) &&& z = (x &&& z) ^^^ (y &&& z) := by
  rw [BitVec.and_comm, and_xor_left, BitVec.and_comm z, BitVec.and_comm z]

theorem rotateRight_zero (x : W) : x.rotateRight 0 = x := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  rw [getLsbD_rotateRight_lt _ _ _ hi, Nat.add_zero, Nat.mod_eq_of_lt hi]

theorem ones_and (x : W) : ones &&& x = x := BitVec.allOnes_and
theorem and_ones (x : W) : x &&& ones = x := BitVec.and_allOnes

theorem cst_ror (c : Bool) (n : Nat) : (cst c).rotateRight n = cst c := by
  cases c
  · exact rotateRight_zero' n
  · exact ones_ror n

theorem rotateRight_rotateRight (x : W) (a n : Nat) :
    (x.rotateRight a).rotateRight n = x.rotateRight ((a + n) % 64) := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [getLsbD_rotateRight_lt _ _ _ hi, getLsbD_rotateRight_lt _ _ _ (Nat.mod_lt _ (by decide : 0 < 64))]
  congr 1
  omega

theorem lin_keyIns (k : Nat) (l : List Nat) : lin V (keyIns k l) = key V k ^^^ lin V l := by
  induction l with
  | nil => simp [keyIns, lin]
  | cons j l ih =>
    simp only [keyIns]
    split
    · subst_vars; simp [lin, ← BitVec.xor_assoc]
    · split
      · rfl
      · simp only [lin, List.foldr_cons] at ih ⊢
        rw [ih, ← BitVec.xor_assoc, ← BitVec.xor_assoc, BitVec.xor_comm (key V j)]

theorem lin_linXor (a b : List Nat) : lin V (linXor a b) = lin V a ^^^ lin V b := by
  induction a with
  | nil => simp [linXor, lin]
  | cons k a ih =>
    simp only [linXor, List.foldr_cons] at ih ⊢
    rw [lin_keyIns, ih]
    simp only [lin, List.foldr_cons, BitVec.xor_assoc]

theorem key_ror (k n : Nat) : key V (k / 64 * 64 + (k % 64 + n) % 64) = (key V k).rotateRight n := by
  have h1 : (k / 64 * 64 + (k % 64 + n) % 64) / 64 = k / 64 := by omega
  have h2 : (k / 64 * 64 + (k % 64 + n) % 64) % 64 = (k % 64 + n) % 64 := by omega
  simp only [key, h1, h2, rotateRight_rotateRight]

theorem lin_linRor (n : Nat) (l : List Nat) : lin V (linRor n l) = (lin V l).rotateRight n := by
  induction l with
  | nil => simp only [linRor, lin, List.map_nil, List.foldr_nil]; exact (rotateRight_zero' n).symm
  | cons k l ih =>
    simp only [linRor, lin, List.map_cons, List.foldr_cons] at ih ⊢
    rw [ih, key_ror, rotateRight_xor]

theorem linCmp_eq : ∀ {a b : List Nat}, linCmp a b = .eq → a = b
  | [], [], _ => rfl
  | [], _ :: _, h => by simp [linCmp] at h
  | _ :: _, [], h => by simp [linCmp] at h
  | x :: a, y :: b, h => by
    simp only [linCmp] at h
    split at h
    · cases h
    · split at h
      · cases h
      · rw [show x = y by omega, linCmp_eq h]

theorem mono_atomIns (a : List Nat) (m : List (List Nat)) :
    mono V (atomIns a m) = lin V a &&& mono V m := by
  induction m with
  | nil => simp [atomIns, mono]
  | cons b m ih =>
    simp only [atomIns]
    split
    · rename_i h; rw [linCmp_eq h]; simp [mono, ← BitVec.and_assoc]
    · rfl
    · simp only [mono, List.foldr_cons] at ih ⊢
      rw [ih, ← BitVec.and_assoc, ← BitVec.and_assoc, BitVec.and_comm (lin V b)]

theorem mono_monoMul (a b : List (List Nat)) : mono V (monoMul a b) = mono V a &&& mono V b := by
  induction a with
  | nil => simp only [monoMul, mono, List.foldr_nil, ones_and]
  | cons k a ih =>
    simp only [monoMul, List.foldr_cons] at ih ⊢
    rw [mono_atomIns, ih]
    simp only [mono, List.foldr_cons, BitVec.and_assoc]

theorem monoCmp_eq : ∀ {a b : List (List Nat)}, monoCmp a b = .eq → a = b
  | [], [], _ => rfl
  | [], _ :: _, h => by simp [monoCmp] at h
  | _ :: _, [], h => by simp [monoCmp] at h
  | x :: a, y :: b, h => by
    simp only [monoCmp] at h
    split at h
    · rename_i hxy; rw [linCmp_eq hxy, monoCmp_eq h]
    · exact absurd h (by assumption)

theorem monos_monoIns (m : List (List Nat)) (ns : List (List (List Nat))) :
    monos V (monoIns m ns) = mono V m ^^^ monos V ns := by
  induction ns with
  | nil => simp [monoIns, monos]
  | cons n ns ih =>
    simp only [monoIns]
    split
    · rename_i h; rw [monoCmp_eq h]; simp [monos, ← BitVec.xor_assoc]
    · rfl
    · simp only [monos, List.foldr_cons] at ih ⊢
      rw [ih, ← BitVec.xor_assoc, ← BitVec.xor_assoc, BitVec.xor_comm (mono V n)]

theorem monos_monosXor (a b : List (List (List Nat))) :
    monos V (monosXor a b) = monos V a ^^^ monos V b := by
  induction a with
  | nil => simp [monosXor, monos]
  | cons k a ih =>
    simp only [monosXor, List.foldr_cons] at ih ⊢
    rw [monos_monoIns, ih]
    simp only [monos, List.foldr_cons, BitVec.xor_assoc]

theorem cst_xor (a b : Bool) : cst (a ^^ b) = cst a ^^^ cst b := by
  cases a <;> cases b <;> simp [cst]

theorem eval_pxor (p q : Poly) : eval V (pxor p q) = eval V p ^^^ eval V q := by
  simp only [eval, pxor, lin_linXor, monos_monosXor]
  rw [cst_xor]
  ac_rfl

theorem mono_ror (n : Nat) (m : List (List Nat)) :
    mono V (m.map (linRor n)) = (mono V m).rotateRight n := by
  induction m with
  | nil => simp only [mono, List.map_nil, List.foldr_nil, ones_ror]
  | cons a m ih =>
    simp only [mono, List.map_cons, List.foldr_cons] at ih ⊢
    rw [ih, lin_linRor, rotateRight_and]

theorem monos_ror (n : Nat) (ns : List (List (List Nat))) :
    monos V (ns.map (·.map (linRor n))) = (monos V ns).rotateRight n := by
  induction ns with
  | nil => simp [monos, rotateRight_zero']
  | cons m ns ih =>
    simp only [monos, List.map_cons, List.foldr_cons] at ih ⊢
    rw [ih, mono_ror, rotateRight_xor]

theorem eval_pror (n : Nat) (p : Poly) : eval V (pror n p) = (eval V p).rotateRight n := by
  simp only [eval, pror, lin_linRor, monos_ror, rotateRight_xor, cst_ror]

theorem monos_append (a b : List (List (List Nat))) : monos V (a ++ b) = monos V a ^^^ monos V b := by
  induction a with
  | nil => simp [monos]
  | cons m a ih => simp only [monos, List.cons_append, List.foldr_cons] at ih ⊢; rw [ih, BitVec.xor_assoc]

theorem monos_cst (c : Bool) : monos V (if c then [[]] else []) = cst c := by
  cases c
  · rfl
  · simp only [monos, mono, cst, ite_true, List.foldr_cons, List.foldr_nil, xor_zero']

theorem monos_lin (l : List Nat) : monos V (if l.isEmpty then [] else [[l]]) = lin V l := by
  cases l with
  | nil => rfl
  | cons k l =>
    simp only [List.isEmpty_cons, Bool.false_eq_true, ite_false, monos, mono, List.foldr_cons,
      List.foldr_nil, and_ones, xor_zero']

theorem eval_terms (p : Poly) : monos V (terms p) = eval V p := by
  simp only [terms, monos_append, eval, monos_cst, monos_lin]
  ac_rfl

theorem cst_not (c : Bool) : cst (!c) = ones ^^^ cst c := by
  cases c <;> simp [cst]

theorem eval_addMono (m : List (List Nat)) (p : Poly) : eval V (addMono m p) = mono V m ^^^ eval V p := by
  unfold addMono
  split
  · simp only [eval, mono, List.foldr_nil, cst_not]
    ac_rfl
  · simp only [eval, mono, List.foldr_cons, List.foldr_nil, and_ones, lin_linXor, BitVec.xor_assoc]
  · simp only [eval, monos_monoIns]
    ac_rfl

theorem eval_zero : eval V zero = 0 := by
  simp only [eval, zero, lin, monos, cst, List.foldr_nil, Bool.false_eq_true, ite_false, xor_zero']

theorem eval_one : eval V one = BitVec.allOnes 64 := by
  simp only [eval, one, lin, monos, cst, List.foldr_nil, ite_true, zero_xor', xor_zero']; rfl

theorem eval_ofMonos (ms : List (List (List Nat))) : eval V (ofMonos ms) = monos V ms := by
  induction ms with
  | nil => exact eval_zero V
  | cons m ms ih => simp only [ofMonos, List.foldr_cons, monos] at ih ⊢; rw [eval_addMono, ih]

theorem monos_map_mul (t : List (List Nat)) (b : List (List (List Nat))) :
    monos V (b.map fun u => monoMul t u) = mono V t &&& monos V b := by
  induction b with
  | nil => simp only [List.map_nil, monos, List.foldr_nil, and_zero']
  | cons u b ih =>
    simp only [monos, List.map_cons, List.foldr_cons] at ih ⊢
    rw [ih, mono_monoMul, and_xor_left]

theorem monos_mul (a b : List (List (List Nat))) :
    monos V (a.flatMap fun t => b.map fun u => monoMul t u) = monos V a &&& monos V b := by
  induction a with
  | nil => simp only [List.flatMap_nil, monos, List.foldr_nil, zero_and']
  | cons t a ih =>
    rw [List.flatMap_cons, monos_append, ih, monos_map_mul]
    simp only [monos, List.foldr_cons]
    rw [and_xor_right]

theorem eval_pand (p q : Poly) : eval V (pand p q) = eval V p &&& eval V q := by
  rw [pand, eval_ofMonos, monos_mul, eval_terms, eval_terms]

theorem or_eq (x y : W) : x ||| y = x ^^^ y ^^^ (x &&& y) := by
  apply BitVec.eq_of_getLsbD_eq; intro i _
  simp only [BitVec.getLsbD_or, BitVec.getLsbD_xor, BitVec.getLsbD_and]
  cases x.getLsbD i <;> cases y.getLsbD i <;> rfl

theorem eval_por (p q : Poly) : eval V (por p q) = eval V p ||| eval V q := by
  rw [por, eval_pxor, eval_pxor, eval_pand, or_eq]

theorem eval_atom (a : Nat) : eval V (atom a) = V a := by
  simp only [eval, atom, lin, key, monos, cst, List.foldr_cons, List.foldr_nil, Bool.false_eq_true,
    ite_false, xor_zero', show 64 * a / 64 = a by omega, show 64 * a % 64 = 0 by omega,
    rotateRight_zero]

/-- `Poly` stands for the word it evaluates to. -/
def AnfRel (p : Poly) (x : W) : Prop := eval V p = x

theorem anf_sound : anf.Sound (AnfRel V) where
  xor ha hb h := by
    simp only [anf, Option.some.injEq] at h; subst h
    simp only [AnfRel] at *; rw [eval_pxor, ha, hb]
  and ha hb h := by
    simp only [anf, Option.some.injEq] at h; subst h
    simp only [AnfRel] at *; rw [eval_pand, ha, hb]
  or ha hb h := by
    simp only [anf, Option.some.injEq] at h; subst h
    simp only [AnfRel] at *; rw [eval_por, ha, hb]
  ror ha h := by
    simp only [anf, Option.some.injEq] at h; subst h
    simp only [AnfRel] at *; rw [eval_pror, ha]
  shr _ h := by cases h
  const {v c} h := by
    simp only [anf] at h
    split at h
    · rename_i hv; cases h; subst hv; exact eval_zero V
    · split at h
      · rename_i hv; cases h; subst hv; exact eval_one V
      · cases h

end

end VG.Bitslice.Anf
