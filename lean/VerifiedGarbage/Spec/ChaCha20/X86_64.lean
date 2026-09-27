import VerifiedGarbage.Spec.ChaCha20
import VerifiedGarbage.TCB.X86_64.Target

/-!
# ChaCha20: the x86-64 contract of the block function

**Trusted** (as every file in `Spec/`). The contract of the assembly
primitive `vg_chacha20_block` on x86-64, in terms of the specification in
`Spec/ChaCha20.lean`.
-/

namespace VG.Spec.ChaCha20

open X86_64 in
/-- x86-64 contract for `vg_chacha20_block(state: *const [u32; 16], buf: *mut [u32; 64])`:
writes `block` of the state at `state` to the first 16 words of `buf`.

The code may read `state` (64 bytes) and read and write `buf` (256 bytes; its
first 64 bytes hold the result on exit, and the rest is scratch space whose
contents on exit are unspecified). `buf` may not overlap `state` or the
return address on the stack. The pointers are public; the state (key,
counter and nonce) is secret. -/
def blockX86_64 : Contract X86_64.isa where
  pre s :=
    let state : Region := ⟨s.gpr .rdi, 64⟩
    let buf : Region := ⟨s.gpr .rsi, 256⟩
    let ret : Region := ⟨s.gpr .rsp, 8⟩
    s.rd = [state] ∧ s.wr = [buf] ∧ buf.Disjoint state ∧ ret.Disjoint buf
  post s s' := stateAt s'.mem (s.gpr .rsi) = block (stateAt s.mem (s.gpr .rdi))
  pub s₁ s₂ := s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi

end VG.Spec.ChaCha20
