import VerifiedGarbage.Proof.Framework.Contract

/-!
# Moving the generic proofs to the shared contracts, once for every hash function

Untrusted: everything here is checked by Lean. The contracts the generic HMAC
and PBKDF2 proofs are written against (`initG`, `finG`, `iterG`) and the
shared contracts of `Spec/Hmac/Generic.lean` and `Spec/Pbkdf2/Generic.lean`
both take the streaming hash function `S` and the scratch space `W` as
parameters, and the implication between them holds for any `S` and `W`:
`generic_implies` proves it once (as `sig_implies`, `Proof/Framework/Contract.lean`,
but for the sizes, which stay symbolic), from the satisfiability of the shared
contract, which each instance proves at its own sizes with `sig_implies_sat`.
-/

namespace VG

/-- Proves `k.Implies k'` as `sig_implies` does, for `k'` built with
`Sig.contract` from a signature whose sizes are symbolic, with `h` the
satisfiability of `k'.pre`. The scratch space is `8 * W` bytes in `k` and
`W * 8` in `k'`. -/
syntax "generic_implies " "[" Lean.Parser.Tactic.simpLemma,* "]" " using " term : tactic
macro_rules
  | `(tactic| generic_implies [$ls,*] using $h) => `(tactic| exact
      { pre := by
          intro s h
          sig_pre [$ls,*] at h
          sig_split h
          sig_reduce [$ls,*]
          sig_simp [$ls,*] []
          sig_and_intros
          all_goals try rw [Nat.mul_comm 8]
          sig_close
          all_goals first
            | with_reducible assumption
            | with_reducible exact Region.Disjoint.symm ‹_›
            | omega
        post := by sig_implies_post [$ls,*]
        pub := by sig_implies_pub [$ls,*]
        sat := $h })

end VG

namespace VG

/-- Proves `∃ s, k'.pre s` with the concrete witness `w`, for `k'` built with
`Sig.contract` (evaluated by unfolding `ls`), whose facts all hold by
evaluation: the disjointness of regions at literal addresses by
`Region.disjoint_of_sep`, the rest by `decide` or `rfl`. -/
syntax "inst_sat " "[" Lean.Parser.Tactic.simpLemma,* "]" " using " term : tactic
macro_rules
  | `(tactic| inst_sat [$ls,*] using $w) => `(tactic| (
      refine ⟨$w, ?_⟩
      first
        | sig_sat_check [$ls,*]
        | (sig_pre [$ls,*]
           sig_and_intros
           all_goals first
             | exact Region.disjoint_of_sep (by decide)
             | decide
             | rfl)))

end VG
