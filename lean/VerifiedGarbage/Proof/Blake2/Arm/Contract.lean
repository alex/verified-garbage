import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Spec.Blake2
import VerifiedGarbage.TCB.Arm.Target

/-!
# BLAKE2 compression function on ARMv7: the contract

The contract the compression functions' proofs are written against, and the
streaming functions use for their calls of them; the artifacts' contract is
the shared one of `Spec/Blake2/Contract.lean`, which implies it.
-/

namespace VG.Proof.Blake2

open VG.Arm VG.Spec.Blake2

/-- The 64-bit offset counter `t` of `compress`: stack arguments 0 (its low
word) and 1. -/
def tArm (s : State) : BitVec 64 := stackArg s 1 ++ stackArg s 0

/-- ARMv7 contract for `compress(state = r0, blocks = r1, n = r2, t, last,
scratch)`, with `t` (64 bits), `last` and `scratch` the stack arguments 0–1,
2 and 3 (AAPCS: `t` cannot take `r3`, so it and every argument after it are
on the stack): updates the state at `state` with the `n` blocks at `blocks`,
block `i` with the counter `t + bb · i` and the final block flag if
`last ≠ 0`. It reads the blocks and the 16 bytes of stack arguments, and
reads and writes the state and 512 bytes of scratch space; the writable
buffers overlap nothing else, and nothing wraps around the end of the
(32-bit) address space. `sp`, the pointers, `n`, `t` and `last` are
public. -/
def compressArm {w : Nat} (P : Params w) : Contract Arm.isa where
  pre s :=
    let state : Region := ⟨State.addr (s.gpr .r0), 8 * (w / 8)⟩
    let blocks : Region := ⟨State.addr (s.gpr .r1), blockBytes w * (s.gpr .r2).toNat⟩
    let scratch : Region := ⟨State.addr (stackArg s 3), 512⟩
    let args : Region := ⟨stackArgAddr s 0, 16⟩
    s.rd = [blocks, args] ∧ s.wr = [state, scratch] ∧
    state.Disjoint scratch ∧ blocks.Disjoint state ∧ blocks.Disjoint scratch ∧
    args.Disjoint state ∧ args.Disjoint scratch ∧
    (s.gpr .r0).toNat + 8 * (w / 8) ≤ 2 ^ 32 ∧
    (s.gpr .r1).toNat + blockBytes w * (s.gpr .r2).toNat ≤ 2 ^ 32 ∧
    (stackArg s 3).toNat + 512 ≤ 2 ^ 32 ∧ s.sp.toNat + 16 ≤ 2 ^ 32
  post s s' := stateAt w s'.mem (State.addr (s.gpr .r0)) =
    compressBlocks P (stateAt w s.mem (State.addr (s.gpr .r0))) s.mem (State.addr (s.gpr .r1))
      (s.gpr .r2).toNat (tArm s).toNat (stackArg s 2 != 0)
  pub s₁ s₂ := s₁.sp = s₂.sp ∧ s₁.gpr .r0 = s₂.gpr .r0 ∧ s₁.gpr .r1 = s₂.gpr .r1 ∧
    s₁.gpr .r2 = s₂.gpr .r2 ∧ stackArg s₁ 0 = stackArg s₂ 0 ∧ stackArg s₁ 1 = stackArg s₂ 1 ∧
    stackArg s₁ 2 = stackArg s₂ 2 ∧ stackArg s₁ 3 = stackArg s₂ 3

end VG.Proof.Blake2
