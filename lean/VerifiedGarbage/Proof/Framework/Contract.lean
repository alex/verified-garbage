import Mathlib.Tactic.CasesM
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.TCB.Artifact

/-!
# Moving a proof from one contract to a stronger one

Untrusted: everything here is checked by Lean.

The proofs are written against per-target contracts (`Proof/<Alg>/<Target>/Contract.lean`);
the artifacts are emitted with the shared contracts of `Spec/`, built with
`Sig.contract`. `Contract.Implies k k'` says that `k'` asks no more of the
code than `k` does, so a proof of `Verified T c k` gives `Verified T c k'`.
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

theorem BitVec.toNat_setWidth_32_64 (x : BitVec 32) : (x.setWidth 64).toNat = x.toNat := by
  simp [BitVec.toNat_setWidth]; omega

theorem BitVec.setWidth_32_64_32 (x : BitVec 32) : (x.setWidth 64).setWidth 32 = x := by
  simp

theorem BitVec.append_32_inj {a b c d : BitVec 32} (h : a ++ b = c ++ d) : a = c ∧ b = d :=
  ⟨by have := congrArg (BitVec.extractLsb' 32 32) h
      rwa [BitVec.extractLsb'_append_eq_left, BitVec.extractLsb'_append_eq_left] at this,
   by have := congrArg (BitVec.extractLsb' 0 32) h
      rwa [BitVec.extractLsb'_append_eq_right, BitVec.extractLsb'_append_eq_right] at this⟩

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

theorem BitVec.setWidth_32_64_inj {a b : BitVec 32} : a.setWidth 64 = b.setWidth 64 ↔ a = b :=
  ⟨fun h => by simpa using congrArg (BitVec.setWidth 32) h, fun h => h ▸ rfl⟩

theorem BitVec.append_32_iff {a b c d : BitVec 32} : a ++ b = c ++ d ↔ a = c ∧ b = d :=
  ⟨BitVec.append_32_inj, fun ⟨h₁, h₂⟩ => h₁ ▸ h₂ ▸ rfl⟩

theorem Curry.apply_const {α : Type} (a : α) :
    ∀ (ws : List ArgWord) (vs : List (BitVec 64)), Curry.apply ws (Curry.const a ws) vs = a
  | [], _ => rfl
  | _ :: ws, [] => Curry.apply_const a ws []
  | _ :: ws, _ :: vs => Curry.apply_const a ws vs

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

end VG
