import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Spec.Blake2
import VerifiedGarbage.TCB.X86.Target

/-!
# BLAKE2b compression function on x86 (32-bit): the contract

Untrusted: everything here is checked by Lean. The contract the proof of the
compression function is written against; the artifact's contract is the
shared one of `Spec/Blake2/Contract.lean`, which implies it.
-/

namespace VG.Proof.Blake2.X86.CompressB

open VG.X86 VG.Spec.Blake2

/-- x86 (32-bit) contract for `compress(state, blocks, n, t, last, scratch)`, whose
arguments are on the stack (cdecl: `state`, `blocks`, `n`, the low and high
words of `t`, `last`, `scratch`): updates the state at `state` with the `n`
blocks at `blocks`, block `i` with the counter `t + 128 · i` and the final
block flag if `last ≠ 0`.

The code may read the arguments (28 bytes above the return address) and the
blocks, and read and write the state (64 bytes) and `scratch` (512 bytes),
which do not overlap each other, the blocks, the arguments or the return
address; nothing wraps around the end of the (32-bit) address space. `esp`
and the arguments are public. -/
def compressX86 : Contract isa where
  pre s :=
    let state : Region := ⟨(arg s 0).setWidth 64, 64⟩
    let blocks : Region := ⟨(arg s 1).setWidth 64, 128 * (arg s 2).toNat⟩
    let scratch : Region := ⟨(arg s 6).setWidth 64, 512⟩
    let args : Region := ⟨argAddr s 0, 28⟩
    let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
    s.rd = [blocks, args] ∧ s.wr = [state, scratch] ∧
    state.Disjoint scratch ∧ blocks.Disjoint state ∧ blocks.Disjoint scratch ∧
    args.Disjoint state ∧ args.Disjoint scratch ∧ ret.Disjoint state ∧ ret.Disjoint scratch ∧
    (arg s 0).toNat + 64 ≤ 2 ^ 32 ∧ (arg s 1).toNat + 128 * (arg s 2).toNat ≤ 2 ^ 32 ∧
    (arg s 6).toNat + 512 ≤ 2 ^ 32 ∧ (s.gpr .esp).toNat + 32 ≤ 2 ^ 32
  post s s' :=
    stateAt 64 s'.mem ((arg s 0).setWidth 64) =
      compressBlocks b (stateAt 64 s.mem ((arg s 0).setWidth 64)) s.mem ((arg s 1).setWidth 64)
        (arg s 2).toNat (arg s 4 ++ arg s 3).toNat (arg s 5 != 0)
  pub s₁ s₂ := s₁.gpr .esp = s₂.gpr .esp ∧ ∀ i < 7, arg s₁ i = arg s₂ i

end VG.Proof.Blake2.X86.CompressB
