import Mathlib.Tactic.CasesM
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.Sig

/-!
# Moving a proof from one contract to a stronger one

Untrusted: everything here is checked by Lean.

A proof may be written against a contract of its own (which its verified
callers may also use with `WP.call`), with its facts spelled out for the
target; the artifact is emitted with the shared contract of `Spec/`, built
with `Sig.contract`. `Contract.Implies k k'` says that `k'` asks no more of
the code than `k` does, so a proof of `Verified T c k` gives `Verified T c k'`
(`Verified.of_implies`), and the correctness and constant time of `c` under
`k` give `Verified T c k'` (`Verified.of_correct`).

`sig_implies` proves `Contract.Implies k k'` cheaply, with the tactics of
`Proof/Framework/Sig.lean`; `contract_implies`, which searches with `simp_all`,
remains for the proofs not moved to it.
-/

namespace VG

/-- `k'` is at least as strong as `k` for its callers: its precondition implies
that of `k`, the postcondition of `k` implies that of `k'`, public data under
`k'` is public under `k`, and `k'` is satisfiable. -/
structure Contract.Implies {M : ISA} (k k' : Contract M) : Prop where
  pre : ∀ s, k'.pre s → k.pre s
  post : ∀ s s', k'.pre s → k.post s s' → k'.post s s'
  pub : ∀ s₁ s₂, k'.pre s₁ → k'.pre s₂ → k'.pub s₁ s₂ → k.pub s₁ s₂
  sat : ∃ s, k'.pre s

/-- `k` is satisfiable if a contract it implies is. -/
theorem Contract.Implies.sat_left {M : ISA} {k k' : Contract M} (h : k.Implies k') : ∃ s, k.pre s :=
  h.sat.elim fun s hs => ⟨s, h.pre s hs⟩

theorem Verified.of_implies {T : Target} {c : Prog T.isa} {k k' : Contract T.isa}
    (h : Verified T c k) (hk : k.Implies k') : Verified T c k' := by
  obtain ⟨hc, hct, -⟩ := h
  refine ⟨fun s hs => ?_, fun s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hp e₁ e₂ => ?_, hk.sat⟩
  · obtain ⟨t, s', he, ha, hp⟩ := hc s (hk.pre s hs)
    exact ⟨t, s', he, ha, hk.post s s' hs hp⟩
  · exact hct s₁ s₂ t₁ t₂ s₁' s₂' (hk.pre _ h₁) (hk.pre _ h₂) (hk.pub _ _ h₁ h₂ hp) e₁ e₂

/-- `Verified` from the correctness and constant time of `c` under a contract
`k` that `k'` implies: the proofs of a function against the contract its
verified callers use, moved to its shared contract. -/
theorem Verified.of_correct {T : Target} {c : Prog T.isa} {k k' : Contract T.isa}
    (hc : ∀ s, k.pre s → ∃ t s', Exec T.isa c s t s' ∧ T.abiPreserved s s' ∧ k.post s s')
    (hct : ConstantTime T.isa k.pre k.pub c) (hk : k.Implies k') : Verified T c k' := by
  refine ⟨fun s hs => ?_, fun s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hp e₁ e₂ => ?_, hk.sat⟩
  · obtain ⟨t, s', he, ha, hp⟩ := hc s (hk.pre s hs)
    exact ⟨t, s', he, ha, hk.post s s' hs hp⟩
  · exact hct s₁ s₂ t₁ t₂ s₁' s₂' (hk.pre _ h₁) (hk.pre _ h₂) (hk.pub _ _ h₁ h₂ hp) e₁ e₂

theorem Region.disjoint_comm {a b : Region} : a.Disjoint b ↔ b.Disjoint a :=
  ⟨Region.Disjoint.symm, Region.Disjoint.symm⟩

/-- Regions that do not wrap around and lie one after the other are disjoint:
for regions at literal addresses, the hypotheses are closed by `decide`. -/
theorem Region.disjoint_of_le {r₁ r₂ : Region}
    (h : r₁.base.toNat + r₁.len ≤ r₂.base.toNat ∨ r₂.base.toNat + r₂.len ≤ r₁.base.toNat)
    (h₁ : r₁.base.toNat + r₁.len ≤ 2 ^ 64) (h₂ : r₂.base.toNat + r₂.len ≤ 2 ^ 64) : r₁.Disjoint r₂ := by
  intro a c₁ c₂
  simp only [Region.Contains] at c₁ c₂
  bv_omega

/-! ## Tactics

Each takes the definitions to unfold: the contracts, the signature and the
calling convention (and its helpers). -/

/-- Unfolds a `Sig.contract` in `h` and in the goal, evaluating the signature. -/
syntax "sig_unfold " "[" Lean.Parser.Tactic.simpLemma,* "]" (Lean.Parser.Tactic.location)? : tactic
macro_rules
  | `(tactic| sig_unfold [$ls,*] $[$loc]?) => `(tactic| (
      set_option linter.unusedSimpArgs false in
      dsimp only [$ls,*, Sig.contract, Sig.words, Param.words, List.flatMap, List.flatten,
        List.map, List.append, ArgWord.bits, IntTy.bits, Sig.retBits, stackBelow] $[$loc]?
      set_option linter.unusedSimpArgs false in
      simp [$ls,*, Sig.bufs, Elem.size, List.pairwise_cons, Curry.apply, Curry.apply_const, Curry.const,
        ArgWord.ofRaw, -BitVec.toNat_setWidth, BitVec.toNat_setWidth_32_64,
        BitVec.setWidth_32_64_32, Param.pubs, stackBelow] $[$loc]?))

/-- Proves `∀ s, k'.pre s → k.pre s`, for `k'` built with `Sig.contract`. The
hypothesis is split into its facts once, and each fact of `k.pre` is closed from
them directly (up to the symmetry of `Region.Disjoint`, or by `omega`); only
what that leaves goes to `simp_all`, which simplifies every hypothesis again
for every goal. -/
syntax "implies_pre " "[" Lean.Parser.Tactic.simpLemma,* "]" : tactic
macro_rules
  | `(tactic| implies_pre [$ls,*]) => `(tactic| (
      intro s h
      sig_unfold [$ls,*] at h
      set_option linter.unusedSimpArgs false in
      simp only [$ls,*]
      all_goals casesm* _ ∧ _
      all_goals and_intros
      all_goals first
        | with_reducible assumption
        | with_reducible exact Region.Disjoint.symm (by with_reducible assumption)
        | omega
        | simp_all [Region.disjoint_comm, Nat.mul_comm]))

/-- Proves `∀ s s', k'.pre s → k.post s s' → k'.post s s'`, for `k'` built with
`Sig.contract`. -/
syntax "implies_post " "[" Lean.Parser.Tactic.simpLemma,* "]" : tactic
macro_rules
  | `(tactic| implies_post [$ls,*]) => `(tactic| (
      intro s s' _ h
      sig_unfold [$ls,*]
      set_option linter.unusedSimpArgs false in
      simp only [$ls,*] at h
      all_goals simpa [Nat.mul_comm] using h))

/-- Proves `∀ s₁ s₂, k'.pre s₁ → k'.pre s₂ → k'.pub s₁ s₂ → k.pub s₁ s₂`, for
`k'` built with `Sig.contract`. -/
syntax "implies_pub " "[" Lean.Parser.Tactic.simpLemma,* "]" : tactic
macro_rules
  | `(tactic| implies_pub [$ls,*]) => `(tactic| (
      rintro s₁ s₂ - - h
      sig_unfold [$ls,*] at h
      set_option linter.unusedSimpArgs false in
      simp only [$ls,*, Nat.forall_lt_succ_right, Nat.not_lt_zero, false_imp_iff, forall_const,
        true_and]
      all_goals
        obtain ⟨_, h⟩ := h
        have := h 0; have := h 1; have := h 2; have := h 3; have := h 4; have := h 5; have := h 6
        have := h 7; have := h 8; have := h 9
        clear h
        -- The widths are in the types of the equations: only `dsimp` can rewrite them.
        dsimp only [List.getD, List.getElem?_cons_succ, List.getElem?_cons_zero, List.getElem?_nil,
          Option.getD_some, Option.getD_none] at *
        simp [BitVec.setWidth_32_64_inj, BitVec.append_32_iff] at *
      all_goals and_intros
      all_goals simp_all))

/-- Proves `∃ s, k'.pre s` with the witness `w`, for `k'` built with `Sig.contract`. -/
syntax "implies_sat " "[" Lean.Parser.Tactic.simpLemma,* "]" " using " term : tactic
macro_rules
  | `(tactic| implies_sat [$ls,*] using $w) => `(tactic| (
      refine ⟨$w, ?_⟩
      sig_unfold [$ls,*]
      all_goals and_intros
      all_goals first
        | exact Region.disjoint_of_le (by decide) (by decide) (by decide)
        | rfl
        | decide
        | exact Region.disjoint_of_sep (by decide)
        | (intro a h₁ h₂; simp only [Region.Contains] at h₁ h₂; bv_omega)))

/-- Proves `k.Implies k'` for `k'` built with `Sig.contract`, with the witness
`w` for the satisfiability of `k'.pre` (and further definitions to unfold to
evaluate `k'.pre` on it). -/
syntax "contract_implies " "[" Lean.Parser.Tactic.simpLemma,* "]"
  " [" Lean.Parser.Tactic.simpLemma,* "]" " using " term : tactic
macro_rules
  | `(tactic| contract_implies [$ls,*] [$ws,*] using $w) => `(tactic| exact
      { pre := by implies_pre [$ls,*]
        post := by implies_post [$ls,*]
        pub := by implies_pub [$ls,*]
        sat := by implies_sat [$ls,*, $ws,*] using $w })

/-- Two regions that do not wrap around the end of the address space, one
entirely below the other: a check that `decide` evaluates on concrete regions. -/
def Region.sep (a b : Region) : Bool :=
  a.base.toNat + a.len ≤ 2 ^ 64 && b.base.toNat + b.len ≤ 2 ^ 64 &&
    (a.base.toNat + a.len ≤ b.base.toNat || b.base.toNat + b.len ≤ a.base.toNat)

theorem Region.disjoint_of_sep {a b : Region} (h : Region.sep a b = true) : a.Disjoint b := by
  simp only [Region.sep, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h
  intro x h₁ h₂
  simp only [Region.Contains] at h₁ h₂
  bv_omega

/-! ## Cheap implications

`sig_implies [ls] [ws] using w` proves `k.Implies k'` for `k'` built with
`Sig.contract` and `k` (unfolded by `ls`: both contracts, the signature and
the calling convention) a contract whose precondition is a conjunction of facts
that each follow from one of `k'`'s (as `sig_pre` evaluates it) by
`assumption`, by symmetry of `Region.Disjoint` or by `omega`, whose
postcondition is `k'`'s as `sig_post` evaluates it, and whose public data
are equalities among `k'`'s. `w` is a state satisfying
`k'.pre`, and `ws` unfolds what `k'.pre` needs to evaluate on it. Unlike
`contract_implies`, nothing searches over all hypotheses with `simp`. -/

/-- Splits the conjunction `h` into anonymous hypotheses. -/
syntax "split_ands_at " ident : tactic
macro_rules
  | `(tactic| split_ands_at $h) => `(tactic| repeat (obtain ⟨_, $h:ident⟩ := $h:ident))

/-- Proves `∀ s, k'.pre s → k.pre s` (see `sig_implies`). -/
syntax "sig_implies_pre " "[" Lean.Parser.Tactic.simpLemma,* "]" " [" Lean.Parser.Tactic.simpLemma,* "]" :
  tactic
macro_rules
  | `(tactic| sig_implies_pre [$ls,*] [$ks,*]) => `(tactic| (
      intro s h
      sig_pre [$ls,*] at h
      split_ands_at h
      set_option linter.unusedSimpArgs false in
      dsimp only [$ks,*]
      and_intros
      all_goals first
        | with_reducible assumption
        | with_reducible exact Region.Disjoint.symm ‹_›
        | omega
        | (simp only [Nat.mul_comm] at *
           first | with_reducible assumption | with_reducible exact Region.Disjoint.symm ‹_›)
        | simp only [*, List.mem_cons, List.mem_singleton, true_or, or_true]))

/-- Proves `∀ s s', k'.pre s → k.post s s' → k'.post s s'` (see `sig_implies`). -/
syntax "sig_implies_post " "[" Lean.Parser.Tactic.simpLemma,* "]" " [" Lean.Parser.Tactic.simpLemma,* "]" :
  tactic
macro_rules
  | `(tactic| sig_implies_post [$ls,*] [$ks,*]) => `(tactic| (
      intro s s' _ h
      sig_post [$ls,*]
      set_option linter.unusedSimpArgs false in
      dsimp only [$ks,*] at h
      exact h))

/-- Proves `∀ s₁ s₂, k'.pre s₁ → k'.pre s₂ → k'.pub s₁ s₂ → k.pub s₁ s₂` (see
`sig_implies`). -/
syntax "sig_implies_pub " "[" Lean.Parser.Tactic.simpLemma,* "]" " [" Lean.Parser.Tactic.simpLemma,* "]" :
  tactic
macro_rules
  | `(tactic| sig_implies_pub [$ls,*] [$ks,*]) => `(tactic| (
      intro s₁ s₂ _ _ h
      sig_pub [$ls,*] at h
      split_ands_at h
      set_option linter.unusedSimpArgs false in
      simp only [$ks,*, Nat.forall_lt_succ_right, Nat.not_lt_zero, false_imp_iff, forall_const,
        true_and]
      and_intros
      all_goals with_reducible assumption))

/-- Proves `∃ s, k'.pre s` with the witness `w`, whose facts (`rd`, `wr`,
bounds) hold by `rfl` or `decide`, and whose disjointness facts follow by
`bv_omega` once `ws` (e.g. `w` itself) evaluates its regions (see
`sig_implies`). -/
syntax "sig_implies_sat " "[" Lean.Parser.Tactic.simpLemma,* "]" " [" Lean.Parser.Tactic.simpLemma,* "]"
  " using " term : tactic
macro_rules
  | `(tactic| sig_implies_sat [$ls,*] [$ws,*] using $w) => `(tactic| (
      refine ⟨$w, ?_⟩
      sig_pre [$ls,*]
      and_intros
      all_goals first
        | rfl
        | decide
        | exact Region.disjoint_of_sep (by decide)
        | (intro a h₁ h₂
           set_option linter.unusedSimpArgs false in
           simp only [Region.Contains, $ws,*] at h₁ h₂
           bv_omega)))

syntax "sig_implies " "[" Lean.Parser.Tactic.simpLemma,* "]" " [" Lean.Parser.Tactic.simpLemma,* "]"
  " using " term : tactic
macro_rules
  | `(tactic| sig_implies [$ls,*] [$ws,*] using $w) => `(tactic| exact
      { pre := by sig_implies_pre [$ls,*] [$ls,*]
        post := by sig_implies_post [$ls,*] [$ls,*]
        pub := by sig_implies_pub [$ls,*] [$ls,*]
        sat := by sig_implies_sat [$ls,*] [$ws,*] using $w })

end VG
