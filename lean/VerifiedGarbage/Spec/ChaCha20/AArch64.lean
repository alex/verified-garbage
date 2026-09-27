import VerifiedGarbage.Spec.ChaCha20
import VerifiedGarbage.TCB.AArch64.Target

/-!
# ChaCha20: the AArch64 contract of the block function

**Trusted** (as every file in `Spec/`). The contract of the assembly
primitive `vg_chacha20_block` on AArch64, in terms of the specification in
`Spec/ChaCha20.lean`.
-/

namespace VG.Spec.ChaCha20

open AArch64 in
/-- AArch64 contract for `vg_chacha20_block(state: *const [u32; 16], buf: *mut [u32; 64])`:
writes `block` of the state at `state` to the first 16 words of `buf`.

The same function and Rust signature on every target: the code may
read `state` (64 bytes) and read and write `buf` (256 bytes; its first 64
bytes hold the result on exit, and the rest is unspecified). `buf` may not
overlap `state`. The pointers are public; the state (key, counter and nonce)
is secret. -/
def blockAArch64 : Contract AArch64.isa where
  pre s :=
    let state : Region := ⟨s.gpr .x0, 64⟩
    let buf : Region := ⟨s.gpr .x1, 256⟩
    s.rd = [state] ∧ s.wr = [buf] ∧ buf.Disjoint state
  post s s' := stateAt s'.mem (s.gpr .x1) = block (stateAt s.mem (s.gpr .x0))
  pub s₁ s₂ := s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1

end VG.Spec.ChaCha20
