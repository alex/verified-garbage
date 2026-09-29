import VerifiedGarbage.Spec.ChaCha20
import VerifiedGarbage.TCB.Arm.Target

/-!
# ChaCha20: the 32-bit ARM contracts

**Untrusted**: the contracts the proofs are written against; the artifacts are emitted with the shared contracts of `Spec/`, which imply these (`Contract.Implies`). The contracts of the assembly
primitives `vg_chacha20_block` and `vg_chacha20_xor` on 32-bit ARM, in terms of the specification in
`Spec/ChaCha20.lean`.
-/

namespace VG.Proof.ChaCha20

open Spec.ChaCha20

open Arm in
/-- 32-bit ARM contract for `vg_chacha20_block(state: *const [u32; 16], buf: *mut [u32; 64])`:
writes `block` of the state at `state` to the first 16 words of `buf`.

The same function and Rust signature on every target: the code may
read `state` (64 bytes) and read and write `buf` (256 bytes; its first 64
bytes hold the result on exit, and the rest is scratch space whose contents
on exit are unspecified). `buf` may not overlap `state`, and neither may wrap
around the end of the (32-bit) address space. The pointers are public; the
state (key, counter and nonce) is secret. -/
def blockArm : Contract Arm.isa where
  pre s :=
    let state : Region := ⟨State.addr (s.gpr .r0), 64⟩
    let buf : Region := ⟨State.addr (s.gpr .r1), 256⟩
    s.rd = [state] ∧ s.wr = [buf] ∧ buf.Disjoint state ∧
    (s.gpr .r0).toNat + 64 ≤ 2 ^ 32 ∧ (s.gpr .r1).toNat + 256 ≤ 2 ^ 32
  post s s' :=
    stateAt s'.mem (State.addr (s.gpr .r1)) = block (stateAt s.mem (State.addr (s.gpr .r0)))
  pub s₁ s₂ := s₁.gpr .r0 = s₂.gpr .r0 ∧ s₁.gpr .r1 = s₂.gpr .r1

open Arm in
/-- 32-bit ARM contract for
`vg_chacha20_xor(state: *mut [u32; 16], data: *mut u8, len: usize, buf: *mut [u32; 80])`:
XORs the first `len` bytes of the keystream of the state at `state` into the
`len` bytes at `data`.

The code may read and write `state` (64 bytes; its contents on exit are
unspecified), `data` (`len` bytes) and `buf` (320 bytes of working space).
They may not overlap each other, and none may wrap around the end of the
(32-bit) address space. The return address is in `lr`, not on the stack, and
the code uses no stack. The pointers and the length are public; the state and
the data are secret. -/
def xorArm : Contract Arm.isa where
  pre s :=
    let state : Region := ⟨State.addr (s.gpr .r0), 64⟩
    let data : Region := ⟨State.addr (s.gpr .r1), (s.gpr .r2).toNat⟩
    let buf : Region := ⟨State.addr (s.gpr .r3), 320⟩
    s.rd = [] ∧ s.wr = [state, data, buf] ∧
    state.Disjoint data ∧ state.Disjoint buf ∧ data.Disjoint buf ∧
    (s.gpr .r0).toNat + 64 ≤ 2 ^ 32 ∧ (s.gpr .r1).toNat + (s.gpr .r2).toNat ≤ 2 ^ 32 ∧
    (s.gpr .r3).toNat + 320 ≤ 2 ^ 32
  post s s' :=
    bytesAt s'.mem (State.addr (s.gpr .r1)) (s.gpr .r2).toNat =
      List.zipWith (· ^^^ ·) (bytesAt s.mem (State.addr (s.gpr .r1)) (s.gpr .r2).toNat)
        (keystream (stateAt s.mem (State.addr (s.gpr .r0))) (s.gpr .r2).toNat)
  pub s₁ s₂ :=
    s₁.gpr .r0 = s₂.gpr .r0 ∧ s₁.gpr .r1 = s₂.gpr .r1 ∧ s₁.gpr .r2 = s₂.gpr .r2 ∧
    s₁.gpr .r3 = s₂.gpr .r3

end VG.Proof.ChaCha20
