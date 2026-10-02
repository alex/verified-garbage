import VerifiedGarbage.Spec.Sha256
import VerifiedGarbage.TCB.AArch64.Target

/-!
# SHA-256: the AArch64 contract

The contracts the proofs are written against; the artifacts are emitted with the
shared contracts of `Spec/`, which imply these (`Contract.Implies`). The
contracts of the AArch64 implementations of the compression function and the
streaming interface, in terms of `Spec/Sha256.lean`.

The return address is in the link register `x30`, which the target's
calling convention requires to be preserved (`VG.AArch64.abiPreserved`), not
on the stack, so unlike on x86-64 no region needs to be kept disjoint from it.
-/

namespace VG.Proof.Sha256

open Spec.Sha256

open AArch64 in
/-- AArch64 contract for
`vg_sha256_compress(state: *mut [u32; 8], blocks: *const [u8; 64], n: usize, scratch: *mut [u64; 14])`:
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
    s₁.gpr .x2 = s₂.gpr .x2 ∧ s₁.gpr .x3 = s₂.gpr .x3 ∧ s₁.sp = s₂.sp

open AArch64 in
/-- AArch64 contract for `vg_sha256_init(state: *mut [u8; 96])` and
`vg_sha224_init`, which store the initial hash value `iv`: makes the
streaming state at `state` represent the empty message, hashed from `iv`.

The code may write `state` (96 bytes). The pointer is public. -/
def initAArch64 (iv : HashValue) : Contract AArch64.isa where
  pre s :=
    let state : Region := ⟨s.gpr .x0, 96⟩
    s.rd = [] ∧ s.wr = [state]
  post s s' := ReprFrom iv s'.mem (s.gpr .x0) []
  pub s₁ s₂ := s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.sp = s₂.sp

open AArch64 in
/-- AArch64 contract for
`vg_sha256_update(state: *mut [u8; 96], count: u64, data: *const u8, len: usize, scratch: *mut [u64; 20])`:
if the streaming state at `state` represents a message `m` of `count` bytes
(modulo 2⁶⁴), hashed from any initial hash value `iv`, then afterwards it
represents `m` followed by the `len` bytes at `data`, from `iv`.

The code may read `data` (`len` bytes) and read and write `state` (96
bytes) and `scratch` (160 bytes, whose contents on exit are unspecified).
These may not overlap each other, nor the 16 bytes below the stack pointer
(the frame saving `x30`), which do not wrap around. The pointers, `count` and
`len` are public; the state and the data are secret. -/
def updateAArch64 : Contract AArch64.isa where
  pre s :=
    let state : Region := ⟨s.gpr .x0, 96⟩
    let data : Region := ⟨s.gpr .x2, (s.gpr .x3).toNat⟩
    let scratch : Region := ⟨s.gpr .x4, 160⟩
    let stack : Region := ⟨s.sp - 16, 16⟩
    s.rd = [data] ∧ s.wr = [state, scratch] ∧
    state.Disjoint scratch ∧ data.Disjoint state ∧ data.Disjoint scratch ∧
    16 ≤ s.sp.toNat ∧ stack.Disjoint state ∧ stack.Disjoint data ∧ stack.Disjoint scratch
  post s s' := ∀ iv m, ReprFrom iv s.mem (s.gpr .x0) m → s.gpr .x1 = BitVec.ofNat 64 m.length →
    ReprFrom iv s'.mem (s.gpr .x0) (m ++ bytesAt s.mem (s.gpr .x2) (s.gpr .x3).toNat)
  pub s₁ s₂ :=
    s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.gpr .x2 = s₂.gpr .x2 ∧
    s₁.gpr .x3 = s₂.gpr .x3 ∧ s₁.gpr .x4 = s₂.gpr .x4 ∧ s₁.sp = s₂.sp

open AArch64 in
/-- AArch64 contract for
`vg_sha256_finalize(state: *mut [u8; 96], count: u64, out: *mut [u8; 32], scratch: *mut [u64; 20])`:
if the streaming state at `state` represents a message `m` of `count` bytes
(modulo 2⁶⁴), hashed from the initial hash value `iv`, writes the final hash
value of `m` from `iv` to `out` (the SHA-256 digest if `iv` is `H0`).

The code may read and write `state` (96 bytes, whose contents on exit are
unspecified), `out` (32 bytes) and `scratch` (160 bytes, whose contents on
exit are unspecified). These may not overlap each other, nor the 16 bytes
below the stack pointer (the frame saving `x30`), which do not wrap around.
The pointers and `count` are public; the state is secret. -/
def finalizeAArch64 : Contract AArch64.isa where
  pre s :=
    let state : Region := ⟨s.gpr .x0, 96⟩
    let out : Region := ⟨s.gpr .x2, 32⟩
    let scratch : Region := ⟨s.gpr .x3, 160⟩
    let stack : Region := ⟨s.sp - 16, 16⟩
    s.rd = [] ∧ s.wr = [state, out, scratch] ∧
    state.Disjoint out ∧ state.Disjoint scratch ∧ out.Disjoint scratch ∧
    16 ≤ s.sp.toNat ∧ stack.Disjoint state ∧ stack.Disjoint out ∧ stack.Disjoint scratch
  post s s' := ∀ iv m, ReprFrom iv s.mem (s.gpr .x0) m → s.gpr .x1 = BitVec.ofNat 64 m.length →
    bytesAt s'.mem (s.gpr .x2) 32 = Spec.Sha256.finalHash iv m
  pub s₁ s₂ :=
    s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.gpr .x2 = s₂.gpr .x2 ∧
    s₁.gpr .x3 = s₂.gpr .x3 ∧ s₁.sp = s₂.sp

end VG.Proof.Sha256
