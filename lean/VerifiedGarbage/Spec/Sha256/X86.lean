import VerifiedGarbage.Spec.Sha256
import VerifiedGarbage.TCB.X86.Target

/-!
# SHA-256: the x86 (32-bit) contract

**Trusted** (as every file in `Spec/`). The contract of the x86 (32-bit)
implementation of the compression function, in terms of `Spec/Sha256.lean`.
-/

namespace VG.Spec.Sha256

open X86 in
/-- x86 (32-bit) contract for
`vg_sha256_compress(state: *mut [u32; 8], blocks: *const u8, n: usize, scratch: *mut [u64; 14])`,
whose arguments are on the stack (cdecl): updates the hash value at `state`
with the `n` 64-byte blocks at `blocks`.

The code may read the arguments (16 bytes above the return address) and
`blocks` (`64 * n` bytes), and read and write `state` (32 bytes) and
`scratch` (112 bytes, whose contents on exit are unspecified). The writable
buffers may not overlap each other, the blocks, the arguments or the return
address, and nothing may wrap around the end of the (32-bit) address space.
`esp` and the arguments (the pointers and `n`) are public; the hash value
and the blocks are secret. -/
def compressX86 : Contract X86.isa where
  pre s :=
    let state : Region := ⟨(arg s 0).setWidth 64, 32⟩
    let blocks : Region := ⟨(arg s 1).setWidth 64, 64 * (arg s 2).toNat⟩
    let scratch : Region := ⟨(arg s 3).setWidth 64, 112⟩
    let args : Region := ⟨argAddr s 0, 16⟩
    let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
    s.rd = [blocks, args] ∧ s.wr = [state, scratch] ∧
    state.Disjoint scratch ∧ blocks.Disjoint state ∧ blocks.Disjoint scratch ∧
    args.Disjoint state ∧ args.Disjoint scratch ∧ ret.Disjoint state ∧ ret.Disjoint scratch ∧
    (arg s 0).toNat + 32 ≤ 2 ^ 32 ∧ (arg s 1).toNat + 64 * (arg s 2).toNat ≤ 2 ^ 32 ∧
    (arg s 3).toNat + 112 ≤ 2 ^ 32 ∧ (s.gpr .esp).toNat + 20 ≤ 2 ^ 32
  post s s' :=
    stateAt s'.mem ((arg s 0).setWidth 64) =
      compressBlocks (stateAt s.mem ((arg s 0).setWidth 64)) s.mem ((arg s 1).setWidth 64)
        (arg s 2).toNat
  pub s₁ s₂ :=
    s₁.gpr .esp = s₂.gpr .esp ∧
    arg s₁ 0 = arg s₂ 0 ∧ arg s₁ 1 = arg s₂ 1 ∧ arg s₁ 2 = arg s₂ 2 ∧ arg s₁ 3 = arg s₂ 3

end VG.Spec.Sha256
