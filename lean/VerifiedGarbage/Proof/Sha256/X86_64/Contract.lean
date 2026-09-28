import VerifiedGarbage.Spec.Sha256
import VerifiedGarbage.TCB.X86_64.Target

/-!
# SHA-256: the x86-64 contract

**Untrusted**: the contracts the proofs are written against; the artifacts are emitted with the shared contracts of `Spec/`, which imply these (`Contract.Implies`). The contracts of the x86-64
implementations of the compression function and the streaming interface, in
terms of `Spec/Sha256.lean`.
-/

namespace VG.Proof.Sha256

open Spec.Sha256

open X86_64 in
/-- x86-64 contract for
`vg_sha256_compress(state: *mut [u32; 8], blocks: *const [u8; 64], n: usize, scratch: *mut [u64; 14])`:
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

open X86_64 in
/-- x86-64 contract for `vg_sha256_init(state: *mut [u8; 96])`: makes the
streaming state at `state` represent the empty message.

The code may write `state` (96 bytes), which may not overlap the return
address on the stack. The pointer is public. -/
def initX86_64 : Contract X86_64.isa where
  pre s :=
    let state : Region := ⟨s.gpr .rdi, 96⟩
    let ret : Region := ⟨s.gpr .rsp, 8⟩
    s.rd = [] ∧ s.wr = [state] ∧ ret.Disjoint state
  post s s' := Repr s'.mem (s.gpr .rdi) []
  pub s₁ s₂ := s₁.gpr .rdi = s₂.gpr .rdi

open X86_64 in
/-- x86-64 contract for
`vg_sha256_update(state: *mut [u8; 96], count: u64, data: *const u8, len: usize, scratch: *mut [u64; 20])`:
if the streaming state at `state` represents a message `m` of `count` bytes
(modulo 2⁶⁴), then afterwards it represents `m` followed by the `len` bytes at
`data`.

The code may read `data` (`len` bytes) and read and write `state` (96
bytes) and `scratch` (160 bytes, whose contents on exit are unspecified).
These may not overlap each other, nor the return address on the stack.
The pointers, `count` and `len` are public; the state and the data are
secret. -/
def updateX86_64 : Contract X86_64.isa where
  pre s :=
    let state : Region := ⟨s.gpr .rdi, 96⟩
    let data : Region := ⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩
    let scratch : Region := ⟨s.gpr .r8, 160⟩
    let ret : Region := ⟨s.gpr .rsp, 8⟩
    s.rd = [data] ∧ s.wr = [state, scratch] ∧
    state.Disjoint scratch ∧ data.Disjoint state ∧ data.Disjoint scratch ∧
    ret.Disjoint state ∧ ret.Disjoint scratch
  post s s' := ∀ m, Repr s.mem (s.gpr .rdi) m → s.gpr .rsi = BitVec.ofNat 64 m.length →
    Repr s'.mem (s.gpr .rdi) (m ++ bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat)
  pub s₁ s₂ :=
    s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rdx = s₂.gpr .rdx ∧
    s₁.gpr .rcx = s₂.gpr .rcx ∧ s₁.gpr .r8 = s₂.gpr .r8

open X86_64 in
/-- x86-64 contract for
`vg_sha256_finalize(state: *mut [u8; 96], count: u64, out: *mut [u8; 32], scratch: *mut [u64; 20])`:
if the streaming state at `state` represents a message `m` of `count` bytes
(modulo 2⁶⁴), writes the SHA-256 digest of `m` to `out`.

The code may read and write `state` (96 bytes, whose contents on exit are
unspecified), `out` (32 bytes) and `scratch` (160 bytes, whose contents on
exit are unspecified). These may not overlap each other, nor the return
address on the stack. The pointers and `count` are public; the state is
secret. -/
def finalizeX86_64 : Contract X86_64.isa where
  pre s :=
    let state : Region := ⟨s.gpr .rdi, 96⟩
    let out : Region := ⟨s.gpr .rdx, 32⟩
    let scratch : Region := ⟨s.gpr .rcx, 160⟩
    let ret : Region := ⟨s.gpr .rsp, 8⟩
    s.rd = [] ∧ s.wr = [state, out, scratch] ∧
    state.Disjoint out ∧ state.Disjoint scratch ∧ out.Disjoint scratch ∧
    ret.Disjoint state ∧ ret.Disjoint out ∧ ret.Disjoint scratch
  post s s' := ∀ m, Repr s.mem (s.gpr .rdi) m → s.gpr .rsi = BitVec.ofNat 64 m.length →
    bytesAt s'.mem (s.gpr .rdx) 32 = Spec.Sha256.hash m
  pub s₁ s₂ :=
    s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rdx = s₂.gpr .rdx ∧
    s₁.gpr .rcx = s₂.gpr .rcx

end VG.Proof.Sha256
