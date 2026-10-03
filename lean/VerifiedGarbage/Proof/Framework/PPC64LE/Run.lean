import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec

/-!
# Running short PPC64LE blocks symbolically

Untrusted: everything here is checked by Lean. `crun [h, …]` proves `WP isa
(.block is) s Q` for a short block by running it with `runBlock_cons`,
`runStep_some` and `runBlock_nil`, unfolding each instruction's semantics
and simplifying with the given facts, as AArch64's does. It suits blocks of
a few instructions; longer ones are composed from them.
-/

namespace VG.PPC64LE

syntax "crun" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic
macro_rules
  | `(tactic| crun) => `(tactic| crun [])
  | `(tactic| crun [$ls,*]) => `(tactic| (
      apply WP.of_runBlock
      set_option linter.unusedSimpArgs false in
      simp (config := { decide := true }) only [runBlock_cons, runStep_some, runBlock_nil,
        exec, State.read, State.write, addr, State.load, State.store, Size.bytes, Size.bits, Size.ext,
        BitVec.setWidth_eq, BitVec.add_zero, BitVec.ofNat_eq_ofNat,
        Mem.read, BitVec.zero_width_append, BitVec.cast_eq, Option.bind_some, Option.map_some,
        Option.some.injEq, exists_eq_left', ite_true, ite_false, reduceCtorEq, ne_eq,
        not_false_eq_true, Nat.reduceMul, Nat.reduceMod, Nat.reduceLT, and_self, true_and,
        and_true, $ls,*]))

end VG.PPC64LE
