import VerifiedGarbage.Spec.Sha256
import VerifiedGarbage.TCB.AArch64.Target

/-!
# SHA-256: the AArch64 contract

**Trusted** (as every file in `Spec/`). The contract of the AArch64
implementation of the compression function, in terms of `Spec/Sha256.lean`.
-/

namespace VG.Spec.Sha256

open AArch64 in
/-- AArch64 contract for
`vg_sha256_compress(state: *mut [u32; 8], blocks: *const u8, n: usize, scratch: *mut [u64; 14])`:
updates the hash value at `state` with the `n` 64-byte blocks at `blocks`.

The code may read `blocks` (`64 * n` bytes) and read and write `state`
(32 bytes) and `scratch` (112 bytes, whose contents on exit are unspecified).
These may not overlap each other. The pointers and `n` are public; the hash
value and the blocks are secret. -/
def compressAArch64 : Contract AArch64.isa where
  pre s :=
    let state : Region := ⟨s.gpr .x0, 32⟩
    let blocks : Region := ⟨s.gpr .x1, 64 * (s.gpr .x2).toNat⟩
    let scratch : Region := ⟨s.gpr .x3, 112⟩
    s.rd = [blocks] ∧ s.wr = [state, scratch] ∧
    state.Disjoint scratch ∧ blocks.Disjoint state ∧ blocks.Disjoint scratch
  post s s' :=
    stateAt s'.mem (s.gpr .x0) =
      compressBlocks (stateAt s.mem (s.gpr .x0)) s.mem (s.gpr .x1) (s.gpr .x2).toNat
  pub s₁ s₂ :=
    s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧
    s₁.gpr .x2 = s₂.gpr .x2 ∧ s₁.gpr .x3 = s₂.gpr .x3

end VG.Spec.Sha256
