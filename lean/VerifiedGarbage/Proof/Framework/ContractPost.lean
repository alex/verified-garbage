import VerifiedGarbage.TCB.Artifact

/-!
# Unfolding a contract's postcondition, for the kernel

Untrusted: everything here is checked by Lean.

A postcondition that matches on a function of the entry state (`match
decrypt … with`) is expensive to reach by conversion (`show match … with`,
`dsimp only [c]`): the kernel, comparing `c.post s s'` with the `match`,
unfolds both sides at once, and the `match` unfolds to a `casesOn` whose
scrutinee it then evaluates (the whole decryption, on the bytes in memory),
a second or more. Rewriting with the contract's equation and `post_mk`
(`rw [c, Contract.post_mk]`, then `dsimp only` to beta-reduce) instead leaves
the kernel only syntactically equal terms to compare.
-/

namespace VG

theorem Contract.post_mk {M : ISA} (pre : M.State → Prop) (post pub : M.State → M.State → Prop) :
    (Contract.mk pre post pub).post = post := rfl

end VG
