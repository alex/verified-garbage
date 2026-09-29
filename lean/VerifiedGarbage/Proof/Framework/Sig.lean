import VerifiedGarbage.TCB.Artifact

/-!
# Proving code against a contract built with `Sig.contract`

Untrusted: everything here is checked by Lean.

The contracts of `Spec/` are built with `Sig.contract` from a signature and a
calling convention. For a concrete signature and calling convention, the
tactics here evaluate the parts of such a contract into the plain facts a
proof works with:

* `sig_pre [defs] at h` turns `h : (sig.contract A …).pre s` into a
  conjunction of `A.wf` (if it says anything), `s.rd = […]`, `s.wr = […]`,
  the disjointness of each pair of buffers of which one is writable (in the
  order of the signature), of the reserved regions (the return address and
  the stack below it, in `A.reserved`'s order) and each buffer, the bounds
  `p.toNat + len ≤ 2 ^ ptrBits` of each buffer, and the further
  precondition; `sig_pre [defs]` on the goal does the same to prove it;
* `sig_post [defs]` turns `(sig.contract A …).post s s'` (a goal or, with
  `at`, a hypothesis) into the postcondition applied to the arguments;
* `sig_pub [defs] at h` turns `h : (sig.contract A …).pub s₁ s₂` into
  the equality of the stack pointers, of anything the contract leaks, and of
  each public argument (in the bits of its width).

`defs` are the definitions to unfold: the contract, the signature, the
calling convention and its helpers. Each runs one `dsimp` and one `simp only`
with a fixed set of lemmas, and no search over hypotheses.
-/

namespace VG

theorem BitVec.toNat_setWidth_32_64 (x : BitVec 32) : (x.setWidth 64).toNat = x.toNat := by
  simp [BitVec.toNat_setWidth]; omega

theorem BitVec.setWidth_32_64_32 (x : BitVec 32) : (x.setWidth 64).setWidth 32 = x := by
  simp

theorem BitVec.append_32_inj {a b c d : BitVec 32} (h : a ++ b = c ++ d) : a = c ∧ b = d :=
  ⟨by have := congrArg (BitVec.extractLsb' 32 32) h
      rwa [BitVec.extractLsb'_append_eq_left, BitVec.extractLsb'_append_eq_left] at this,
   by have := congrArg (BitVec.extractLsb' 0 32) h
      rwa [BitVec.extractLsb'_append_eq_right, BitVec.extractLsb'_append_eq_right] at this⟩

theorem BitVec.setWidth_32_64_inj {a b : BitVec 32} : a.setWidth 64 = b.setWidth 64 ↔ a = b :=
  ⟨fun h => by simpa using congrArg (BitVec.setWidth 32) h, fun h => h ▸ rfl⟩

theorem BitVec.append_32_iff {a b c d : BitVec 32} : a ++ b = c ++ d ↔ a = c ∧ b = d :=
  ⟨BitVec.append_32_inj, fun ⟨h₁, h₂⟩ => h₁ ▸ h₂ ▸ rfl⟩

theorem Curry.apply_const {α : Type} (a : α) :
    ∀ (ws : List ArgWord) (vs : List (BitVec 64)), Curry.apply ws (Curry.const a ws) vs = a
  | [], _ => rfl
  | _ :: ws, [] => Curry.apply_const a ws []
  | _ :: ws, _ :: vs => Curry.apply_const a ws vs

/-- The public arguments, one flag at a time. -/
theorem Sig.forall_pubs_cons {P : Nat → Prop} {b : Bool} {l : List Bool} :
    (∀ i, (b :: l).getD i false = true → P i) ↔
      (b = true → P 0) ∧ ∀ i, l.getD i false = true → P (i + 1) :=
  ⟨fun h => ⟨h 0, fun i => h (i + 1)⟩, fun ⟨h₀, h⟩ i => match i with
    | 0 => h₀
    | i + 1 => h i⟩

theorem Sig.forall_pubs_nil {P : Nat → Prop} :
    (∀ i, ([] : List Bool).getD i false = true → P i) ↔ True :=
  ⟨fun _ => trivial, fun _ i h => by simp at h⟩

/-- Unfolds a contract built with `Sig.contract` (at `loc`), evaluating the
signature and the calling convention given by `ls`. -/
syntax "sig_eval " "[" Lean.Parser.Tactic.simpLemma,* "]" (Lean.Parser.Tactic.location)? : tactic
macro_rules
  | `(tactic| sig_eval [$ls,*] $[$loc]?) => `(tactic| (
      set_option linter.unusedSimpArgs false in
      dsimp only [$ls,*, Sig.contract, Sig.words, Param.words, Param.pubs, List.flatMap,
        List.flatten, List.map, List.append, ArgWord.bits, IntTy.bits, Sig.retBits, stackBelow,
        List.length, List.take, List.cons_append, List.nil_append] $[$loc]?
      set_option linter.unusedSimpArgs false in
      simp only [$ls,*, Nat.reduceAdd, Nat.reduceSub, Nat.reduceMul, Nat.reduceDiv,
        Nat.reduceLeDiff, Nat.reduceEqDiff, ↓reduceIte, Sig.bufs, Curry.apply, Curry.const,
        Curry.apply_const, ArgWord.ofRaw, Elem.size, List.filter, List.map, List.cons_append,
        List.nil_append, List.all_cons, List.all_nil, Bool.not_true, Bool.not_false, Bool.and_true,
        Bool.and_false, Bool.true_and, Bool.false_and, Bool.and_self, Bool.or_true, Bool.true_or,
        Bool.or_false, Bool.false_or, Bool.false_eq_true, decide_true, decide_false, Nat.mul_one,
        Nat.one_mul, List.pairwise_cons, List.forall_mem_cons, List.not_mem_nil, List.Pairwise.nil,
        List.mem_cons, List.mem_nil_iff, forall_eq_or_imp, forall_eq, forall_false, implies_true,
        true_implies, false_implies, and_true, true_and, and_self, or_self, or_true, true_or,
        false_or, or_false, and_assoc, Nat.add_zero, List.zip_cons_cons, List.zip_nil_left,
        List.zip_nil_right, List.sum_cons, List.sum_nil, BitVec.setWidth_eq,
        BitVec.setWidth_32_64_32, BitVec.toNat_setWidth_32_64, BitVec.setWidth_setWidth_of_le,
        Sig.forall_pubs_cons, Sig.forall_pubs_nil] $[$loc]?))

/-- Evaluates the precondition of a contract built with `Sig.contract` into
a conjunction of plain facts (see the module documentation). -/
syntax "sig_pre " "[" Lean.Parser.Tactic.simpLemma,* "]" (Lean.Parser.Tactic.location)? : tactic
macro_rules
  | `(tactic| sig_pre [$ls,*] $[$loc]?) => `(tactic| sig_eval [$ls,*] $[$loc]?)

/-- Evaluates the postcondition of a contract built with `Sig.contract`. -/
syntax "sig_post " "[" Lean.Parser.Tactic.simpLemma,* "]" (Lean.Parser.Tactic.location)? : tactic
macro_rules
  | `(tactic| sig_post [$ls,*] $[$loc]?) => `(tactic| sig_eval [$ls,*] $[$loc]?)

/-- Evaluates the public data of a contract built with `Sig.contract` into
equalities. -/
syntax "sig_pub " "[" Lean.Parser.Tactic.simpLemma,* "]" (Lean.Parser.Tactic.location)? : tactic
macro_rules
  | `(tactic| sig_pub [$ls,*] $[$loc]?) => `(tactic| (
      sig_eval [$ls,*] $[$loc]?
      -- The widths are in the types of the equations: only `dsimp` can rewrite them.
      try dsimp only [List.getD, List.getElem?_cons_succ, List.getElem?_cons_zero,
        List.getElem?_nil, Option.getD_some, Option.getD_none, Nat.zero_add] $[$loc]?
      try simp only [BitVec.setWidth_eq, BitVec.setWidth_32_64_32, BitVec.setWidth_32_64_inj,
        BitVec.append_32_iff, and_assoc, and_true, true_and] $[$loc]?))

end VG
