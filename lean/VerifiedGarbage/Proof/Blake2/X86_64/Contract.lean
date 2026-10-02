import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Spec.Blake2
import VerifiedGarbage.TCB.X86_64.Target

/-!
# BLAKE2 compression function on x86-64: the contract

The contract the proof of the compression function is written against, and
which the streaming functions use for their calls of it; the artifacts'
contract is the shared one of `Spec/Blake2/Contract.lean`, which implies it.
-/

namespace VG.Proof.Blake2

open VG.X86_64 VG.Spec.Blake2

/-- x86-64 contract for `compress(state = rdi, blocks = rsi, n = rdx, t = rcx,
last = r8d, scratch = r9)`: updates the state at `state` with the `n` blocks at
`blocks`, block `i` with the counter `t + bb · i` and the final block flag if
`last ≠ 0`. It reads the blocks and reads and writes the state and 512 bytes
of scratch space, which do not overlap each other or the return address. The
pointers, `n`, `t` and `last` are public. -/
def compressX86_64 {w : Nat} (P : Params w) : Contract isa where
  pre s :=
    let state : Region := ⟨s.gpr .rdi, 8 * (w / 8)⟩
    let blocks : Region := ⟨s.gpr .rsi, blockBytes w * (s.gpr .rdx).toNat⟩
    let scratch : Region := ⟨s.gpr .r9, 512⟩
    let ret : Region := ⟨s.gpr .rsp, 8⟩
    s.rd = [blocks] ∧ s.wr = [state, scratch] ∧
    state.Disjoint scratch ∧ blocks.Disjoint state ∧ blocks.Disjoint scratch ∧
    ret.Disjoint state ∧ ret.Disjoint scratch
  post s s' := stateAt w s'.mem (s.gpr .rdi) =
    compressBlocks P (stateAt w s.mem (s.gpr .rdi)) s.mem (s.gpr .rsi) (s.gpr .rdx).toNat
      (s.gpr .rcx).toNat ((s.gpr .r8).setWidth 32 != 0)
  pub s₁ s₂ := s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rdx = s₂.gpr .rdx ∧
    s₁.gpr .rcx = s₂.gpr .rcx ∧ (s₁.gpr .r8).setWidth 32 = (s₂.gpr .r8).setWidth 32 ∧
    s₁.gpr .r9 = s₂.gpr .r9

end VG.Proof.Blake2
