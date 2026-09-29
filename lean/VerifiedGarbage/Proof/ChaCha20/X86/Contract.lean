import VerifiedGarbage.Spec.ChaCha20
import VerifiedGarbage.TCB.X86.Target

/-!
# ChaCha20: the x86 (32-bit) contract of the block function

**Untrusted**: the contract the proof is written against; the artifact is emitted with the shared contract of `Spec/`, which implies this one (`Contract.Implies`). The contract of the assembly
primitive `vg_chacha20_block` on x86 (32-bit), in terms of the specification in
`Spec/ChaCha20.lean`.
-/

namespace VG.Proof.ChaCha20

open Spec.ChaCha20

open X86 in
/-- x86 (32-bit) contract for `vg_chacha20_block(state: *const [u32; 16], buf: *mut [u32; 64])`,
whose arguments are on the stack (cdecl): writes `block` of the state at
`state` to the first 16 words of `buf`.

The same function and Rust signature on every target: the code may
read the two arguments (8 bytes above the return address) and `state` (64
bytes), and read and write `buf` (256 bytes; its first 64 bytes hold the
result on exit, and the rest is scratch space whose contents on exit are
unspecified). `buf` may not overlap `state`, the arguments or the return
address, and nothing may wrap around the end of the (32-bit) address space.
`esp` and the arguments (the pointers) are public; the state (key, counter
and nonce) is secret. -/
def blockX86 : Contract X86.isa where
  pre s :=
    let state : Region := ⟨(arg s 0).setWidth 64, 64⟩
    let buf : Region := ⟨(arg s 1).setWidth 64, 256⟩
    let args : Region := ⟨argAddr s 0, 8⟩
    let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
    s.rd = [state, args] ∧ s.wr = [buf] ∧
    buf.Disjoint state ∧ args.Disjoint buf ∧ ret.Disjoint buf ∧
    (arg s 0).toNat + 64 ≤ 2 ^ 32 ∧ (arg s 1).toNat + 256 ≤ 2 ^ 32 ∧
    (s.gpr .esp).toNat + 12 ≤ 2 ^ 32
  post s s' :=
    stateAt s'.mem ((arg s 1).setWidth 64) = block (stateAt s.mem ((arg s 0).setWidth 64))
  pub s₁ s₂ := s₁.gpr .esp = s₂.gpr .esp ∧ arg s₁ 0 = arg s₂ 0 ∧ arg s₁ 1 = arg s₂ 1

open X86 in
/-- x86 (32-bit) contract for
`vg_chacha20_xor(state: *mut [u32; 16], data: *mut u8, len: usize, buf: *mut [u32; 80])`,
whose arguments are on the stack (cdecl): XORs the first `len` bytes of the
keystream of the state at `state` into the `len` bytes at `data`.

The code may read and write the arguments (16 bytes above the return
address), `state` (64 bytes; its contents on exit are unspecified), `data`
(`len` bytes) and `buf` (320 bytes of working space). These may not overlap
each other; the buffers may not overlap the return address or the 12 bytes
of stack below it, where the calls of the block function store their
arguments and return address; nothing may wrap around the end of the
(32-bit) address space. `esp` and the arguments (the pointers and the length)
are public; the state and the data are secret. -/
def xorX86 : Contract X86.isa where
  pre s :=
    let state : Region := ⟨(arg s 0).setWidth 64, 64⟩
    let data : Region := ⟨(arg s 1).setWidth 64, (arg s 2).toNat⟩
    let buf : Region := ⟨(arg s 3).setWidth 64, 320⟩
    let args : Region := ⟨argAddr s 0, 16⟩
    let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
    let stack : Region := ⟨(s.gpr .esp).setWidth 64 - 12, 12⟩
    s.rd = [] ∧ s.wr = [state, data, buf, args] ∧
    state.Disjoint data ∧ state.Disjoint buf ∧ data.Disjoint buf ∧
    args.Disjoint state ∧ args.Disjoint data ∧ args.Disjoint buf ∧
    ret.Disjoint state ∧ ret.Disjoint data ∧ ret.Disjoint buf ∧
    stack.Disjoint state ∧ stack.Disjoint data ∧ stack.Disjoint buf ∧
    (arg s 0).toNat + 64 ≤ 2 ^ 32 ∧ (arg s 1).toNat + (arg s 2).toNat ≤ 2 ^ 32 ∧
    (arg s 3).toNat + 320 ≤ 2 ^ 32 ∧ 12 ≤ (s.gpr .esp).toNat ∧ (s.gpr .esp).toNat + 20 ≤ 2 ^ 32
  post s s' :=
    bytesAt s'.mem ((arg s 1).setWidth 64) (arg s 2).toNat =
      List.zipWith (· ^^^ ·) (bytesAt s.mem ((arg s 1).setWidth 64) (arg s 2).toNat)
        (keystream (stateAt s.mem ((arg s 0).setWidth 64)) (arg s 2).toNat)
  pub s₁ s₂ := s₁.gpr .esp = s₂.gpr .esp ∧ ∀ i < 4, arg s₁ i = arg s₂ i

end VG.Proof.ChaCha20
