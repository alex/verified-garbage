import VerifiedGarbage.Spec.ChaCha20
import VerifiedGarbage.TCB.Arm.Target

/-!
# ChaCha20: the 32-bit ARM contract of the block function

**Untrusted**: the contracts the proofs are written against; the artifacts are emitted with the shared contracts of `Spec/`, which imply these (`Contract.Implies`). The contract of the assembly
primitive `vg_chacha20_block` on 32-bit ARM, in terms of the specification in
`Spec/ChaCha20.lean`.
-/

namespace VG.Proof.ChaCha20

open Spec.ChaCha20

open Arm in
/-- 32-bit ARM contract for `vg_chacha20_block(state: *const [u32; 16], buf: *mut [u32; 64])`:
writes `block` of the state at `state` to the first 16 words of `buf`.

The same function and Rust signature on every target: the code may
read `state` (64 bytes) and read and write `buf` (256 bytes; its first 64
bytes hold the result on exit, and the rest is scratch space whose contents
on exit are unspecified). `buf` may not overlap `state`, and neither may wrap
around the end of the (32-bit) address space. The pointers are public; the
state (key, counter and nonce) is secret. -/
def blockArm : Contract Arm.isa where
  pre s :=
    let state : Region := ⟨State.addr (s.gpr .r0), 64⟩
    let buf : Region := ⟨State.addr (s.gpr .r1), 256⟩
    s.rd = [state] ∧ s.wr = [buf] ∧ buf.Disjoint state ∧
    (s.gpr .r0).toNat + 64 ≤ 2 ^ 32 ∧ (s.gpr .r1).toNat + 256 ≤ 2 ^ 32
  post s s' :=
    stateAt s'.mem (State.addr (s.gpr .r1)) = block (stateAt s.mem (State.addr (s.gpr .r0)))
  pub s₁ s₂ := s₁.gpr .r0 = s₂.gpr .r0 ∧ s₁.gpr .r1 = s₂.gpr .r1

end VG.Proof.ChaCha20
