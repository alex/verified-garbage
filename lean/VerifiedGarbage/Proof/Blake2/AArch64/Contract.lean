import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Spec.Blake2
import VerifiedGarbage.TCB.AArch64.Target

/-!
# BLAKE2 compression function on AArch64: the contract

Untrusted: everything here is checked by Lean. The contract the streaming
functions use for their calls of the compression function; the artifacts'
contract is the shared one of `Spec/Blake2/Contract.lean`, which implies it.
-/

namespace VG.Proof.Blake2

open VG.AArch64 VG.Spec.Blake2

/-- AArch64 contract for `compress(state = x0, blocks = x1, n = x2, t = x3,
last = w4, scratch = x5)`: updates the state at `state` with the `n` blocks at
`blocks`, block `i` with the counter `t + bb · i` and the final block flag if
`last ≠ 0`. It reads the blocks and reads and writes the state and 512 bytes
of scratch space, which do not overlap each other. The pointers, `n`, `t`
and `last` are public. -/
def compressAArch64 {w : Nat} (P : Params w) : Contract isa where
  pre s :=
    let state : Region := ⟨s.gpr .x0, 8 * (w / 8)⟩
    let blocks : Region := ⟨s.gpr .x1, blockBytes w * (s.gpr .x2).toNat⟩
    let scratch : Region := ⟨s.gpr .x5, 512⟩
    s.rd = [blocks] ∧ s.wr = [state, scratch] ∧
    state.Disjoint scratch ∧ blocks.Disjoint state ∧ blocks.Disjoint scratch
  post s s' := stateAt w s'.mem (s.gpr .x0) =
    compressBlocks P (stateAt w s.mem (s.gpr .x0)) s.mem (s.gpr .x1) (s.gpr .x2).toNat
      (s.gpr .x3).toNat ((s.gpr .x4).setWidth 32 != 0)
  pub s₁ s₂ := s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.gpr .x2 = s₂.gpr .x2 ∧
    s₁.gpr .x3 = s₂.gpr .x3 ∧ (s₁.gpr .x4).setWidth 32 = (s₂.gpr .x4).setWidth 32 ∧
    s₁.gpr .x5 = s₂.gpr .x5 ∧ s₁.sp = s₂.sp

end VG.Proof.Blake2
