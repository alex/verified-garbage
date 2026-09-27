import VerifiedGarbage.Spec.Sha256
import VerifiedGarbage.TCB.X86_64.Target

/-!
# SHA-256: the x86-64 contract

**Trusted** (as every file in `Spec/`). The contract of the x86-64
implementation of the compression function, in terms of `Spec/Sha256.lean`.
-/

namespace VG.Spec.Sha256

open X86_64 in
/-- x86-64 contract for
`vg_sha256_compress(state: *mut [u32; 8], blocks: *const u8, n: usize, scratch: *mut [u64; 14])`:
updates the hash value at `state` with the `n` 64-byte blocks at `blocks`.

The code may read `blocks` (`64 * n` bytes) and read and write `state`
(32 bytes) and `scratch` (112 bytes, whose contents on exit are unspecified).
These may not overlap each other, nor the return address on the stack.
The pointers and `n` are public; the hash value and the blocks are secret. -/
def compressX86_64 : Contract X86_64.isa where
  pre s :=
    let state : Region := ⟨s.gpr .rdi, 32⟩
    let blocks : Region := ⟨s.gpr .rsi, 64 * (s.gpr .rdx).toNat⟩
    let scratch : Region := ⟨s.gpr .rcx, 112⟩
    let ret : Region := ⟨s.gpr .rsp, 8⟩
    s.rd = [blocks] ∧ s.wr = [state, scratch] ∧
    state.Disjoint scratch ∧ blocks.Disjoint state ∧ blocks.Disjoint scratch ∧
    ret.Disjoint state ∧ ret.Disjoint scratch
  post s s' :=
    stateAt s'.mem (s.gpr .rdi) =
      compressBlocks (stateAt s.mem (s.gpr .rdi)) s.mem (s.gpr .rsi) (s.gpr .rdx).toNat
  pub s₁ s₂ :=
    s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧
    s₁.gpr .rdx = s₂.gpr .rdx ∧ s₁.gpr .rcx = s₂.gpr .rcx

end VG.Spec.Sha256
