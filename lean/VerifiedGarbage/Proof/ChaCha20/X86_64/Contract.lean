import VerifiedGarbage.Spec.ChaCha20
import VerifiedGarbage.TCB.X86_64.Target

/-!
# ChaCha20: the x86-64 contract of the block function

**Untrusted**: the contracts the proofs are written against; the artifacts are emitted with the shared contracts of `Spec/`, which imply these (`Contract.Implies`). The contract of the assembly
primitive `vg_chacha20_block` on x86-64, in terms of the specification in
`Spec/ChaCha20.lean`.
-/

namespace VG.Proof.ChaCha20

open Spec.ChaCha20

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

open X86_64 in
/-- x86-64 contract for
`vg_chacha20_xor(state: *mut [u32; 16], data: *mut u8, len: usize, buf: *mut [u32; 80])`:
XORs the first `len` bytes of the keystream of the state at `state` into the
`len` bytes at `data`.

The code may read and write `state` (64 bytes; its contents on exit are
unspecified), `data` (`len` bytes) and `buf` (320 bytes of working space).
They may not overlap each other, the return address on the stack, or the 8
bytes below it, where the call of the block function stores its return
address; `data` does not wrap around the end of the address space. The
pointers and the length are public; the state and the data are secret. -/
def xorX86_64 : Contract X86_64.isa where
  pre s :=
    let state : Region := ⟨s.gpr .rdi, 64⟩
    let data : Region := ⟨s.gpr .rsi, (s.gpr .rdx).toNat⟩
    let buf : Region := ⟨s.gpr .rcx, 320⟩
    let ret : Region := ⟨s.gpr .rsp, 8⟩
    let stack : Region := ⟨s.gpr .rsp - 8, 8⟩
    s.rd = [] ∧ s.wr = [state, data, buf] ∧
    state.Disjoint data ∧ state.Disjoint buf ∧ data.Disjoint buf ∧
    ret.Disjoint state ∧ ret.Disjoint data ∧ ret.Disjoint buf ∧
    stack.Disjoint state ∧ stack.Disjoint data ∧ stack.Disjoint buf ∧
    (s.gpr .rsi).toNat + (s.gpr .rdx).toNat ≤ 2 ^ 64
  post s s' :=
    bytesAt s'.mem (s.gpr .rsi) (s.gpr .rdx).toNat =
      List.zipWith (· ^^^ ·) (bytesAt s.mem (s.gpr .rsi) (s.gpr .rdx).toNat)
        (keystream (stateAt s.mem (s.gpr .rdi)) (s.gpr .rdx).toNat)
  pub s₁ s₂ :=
    s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rdx = s₂.gpr .rdx ∧
    s₁.gpr .rcx = s₂.gpr .rcx ∧ s₁.gpr .rsp = s₂.gpr .rsp

end VG.Proof.ChaCha20
