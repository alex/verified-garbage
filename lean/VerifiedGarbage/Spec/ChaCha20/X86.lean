import VerifiedGarbage.Spec.ChaCha20
import VerifiedGarbage.TCB.X86.Target

/-!
# ChaCha20: the x86 (32-bit) contract of the block function

**Trusted** (as every file in `Spec/`). The contract of the assembly
primitive `vg_chacha20_block` on x86 (32-bit), in terms of the specification in
`Spec/ChaCha20.lean`.
-/

namespace VG.Spec.ChaCha20

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

end VG.Spec.ChaCha20
