import VerifiedGarbage.Spec.ChaCha20
import VerifiedGarbage.TCB.PPC64LE.Target

/-!
# ChaCha20: the PPC64LE contract of the block function

**Untrusted**: the contracts the proofs are written against; the artifacts are emitted with the shared contracts of `Spec/`, which imply these (`Contract.Implies`). The contract of the assembly
primitive `vg_chacha20_block` on PPC64LE, in terms of the specification in
`Spec/ChaCha20.lean`.
-/

namespace VG.Proof.ChaCha20

open Spec.ChaCha20

open PPC64LE in
/-- PPC64LE contract for `vg_chacha20_block(state: *const [u32; 16], buf: *mut [u32; 64])`:
writes `block` of the state at `state` to the first 16 words of `buf`.

The same function and Rust signature on every target: the code may
read `state` (64 bytes) and read and write `buf` (256 bytes; its first 64
bytes hold the result on exit, and the rest is unspecified). `buf` may not
overlap `state`. The pointers are public; the state (key, counter and nonce)
is secret. -/
def blockPPC64LE : Contract PPC64LE.isa where
  pre s :=
    let state : Region := ⟨s.gpr .r3, 64⟩
    let buf : Region := ⟨s.gpr .r4, 256⟩
    s.rd = [state] ∧ s.wr = [buf] ∧ buf.Disjoint state
  post s s' := stateAt s'.mem (s.gpr .r4) = block (stateAt s.mem (s.gpr .r3))
  pub s₁ s₂ := s₁.gpr .r3 = s₂.gpr .r3 ∧ s₁.gpr .r4 = s₂.gpr .r4 ∧ s₁.sp = s₂.sp

end VG.Proof.ChaCha20
