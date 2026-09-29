import VerifiedGarbage.Spec.Sha3.Contract
import VerifiedGarbage.TCB.Arm.Target

/-!
# SHA-3: the 32-bit ARM contracts

**Untrusted**: the contracts the proofs are written against; the artifacts
are emitted with the shared contracts of `Spec/`, which imply these
(`Contract.Implies`), with the arguments where AAPCS passes them.

The return address is in `lr`, which the target's calling convention
requires to be preserved (`VG.Arm.abiPreserved`); the streaming functions
save it in their scratch space around their calls of the permutation, so
they use no stack.
-/

namespace VG.Proof.Sha3

open Spec.Sha3

open Arm in
/-- 32-bit ARM contract for
`vg_keccak_f1600(state: *mut [u64; 25], scratch: *mut [u64; 64])`: applies
Keccak-f[1600] to the state at `state`.

The code may read and write `state` (200 bytes) and `scratch` (512 bytes,
whose contents on exit are unspecified), which may not overlap or wrap
around the end of the (32-bit) address space. The pointers are public; the
state is secret. -/
def permuteArm : Contract Arm.isa where
  pre s :=
    let state : Region := ⟨State.addr (s.gpr .r0), 200⟩
    let scratch : Region := ⟨State.addr (s.gpr .r1), 512⟩
    s.rd = [] ∧ s.wr = [state, scratch] ∧ state.Disjoint scratch ∧
    (s.gpr .r0).toNat + 200 ≤ 2 ^ 32 ∧ (s.gpr .r1).toNat + 512 ≤ 2 ^ 32
  post s s' :=
    stateAt s'.mem (State.addr (s.gpr .r0)) = keccakF (stateAt s.mem (State.addr (s.gpr .r0)))
  pub s₁ s₂ := s₁.gpr .r0 = s₂.gpr .r0 ∧ s₁.gpr .r1 = s₂.gpr .r1

open Arm in
/-- 32-bit ARM contract for `vg_keccak_absorb(state = r0, rate = r1,
pos = r2, data = r3, len = [sp], scratch = [sp, #4]) -> r0`: absorbs `data`
into the streaming state (`Repr`) and returns the new position in the
block.

The code may read the arguments on the stack (8 bytes at `sp`) and `data`,
and read and write `state` (200 bytes) and `scratch` (640 bytes). The
writable buffers may not overlap each other, the data or the arguments, and
nothing may wrap around the end of the (32-bit) address space. `rate` is one
of `rates`, and `pos < rate`. -/
def absorbArm : Contract Arm.isa where
  pre s :=
    let state : Region := ⟨State.addr (s.gpr .r0), 200⟩
    let data : Region := ⟨State.addr (s.gpr .r3), (stackArg s 0).toNat⟩
    let scratch : Region := ⟨State.addr (stackArg s 1), 640⟩
    let args : Region := ⟨stackArgAddr s 0, 8⟩
    s.rd = [data, args] ∧ s.wr = [state, scratch] ∧
    state.Disjoint scratch ∧ data.Disjoint state ∧ data.Disjoint scratch ∧
    args.Disjoint state ∧ args.Disjoint scratch ∧
    (s.gpr .r0).toNat + 200 ≤ 2 ^ 32 ∧ (s.gpr .r3).toNat + (stackArg s 0).toNat ≤ 2 ^ 32 ∧
    (stackArg s 1).toNat + 640 ≤ 2 ^ 32 ∧ s.sp.toNat + 8 ≤ 2 ^ 32 ∧
    (s.gpr .r1).toNat ∈ rates ∧ (s.gpr .r2).toNat < (s.gpr .r1).toNat
  post s s' :=
    (∀ msg, Repr s.mem (State.addr (s.gpr .r0)) (s.gpr .r1).toNat msg →
      (s.gpr .r2).toNat = msg.length % (s.gpr .r1).toNat →
      Repr s'.mem (State.addr (s.gpr .r0)) (s.gpr .r1).toNat
        (msg ++ bytesAt s.mem (State.addr (s.gpr .r3)) (stackArg s 0).toNat)) ∧
    (s'.gpr .r0).toNat = ((s.gpr .r2).toNat + (stackArg s 0).toNat) % (s.gpr .r1).toNat
  pub s₁ s₂ :=
    s₁.sp = s₂.sp ∧ s₁.gpr .r0 = s₂.gpr .r0 ∧ s₁.gpr .r1 = s₂.gpr .r1 ∧ s₁.gpr .r2 = s₂.gpr .r2 ∧
    s₁.gpr .r3 = s₂.gpr .r3 ∧ stackArg s₁ 0 = stackArg s₂ 0 ∧ stackArg s₁ 1 = stackArg s₂ 1

open Arm in
/-- 32-bit ARM contract for `vg_keccak_pad(state = r0, rate = r1, pos = r2,
suffix = r3, scratch = [sp])`: absorbs the padding (with the low byte of
`suffix`) into the streaming state.

The code may read the argument on the stack (4 bytes at `sp`), and read and
write `state` (200 bytes) and `scratch` (640 bytes), which may not overlap
each other or the argument, or wrap around the end of the (32-bit) address
space. `rate` is one of `rates`, and `pos < rate`. -/
def padArm : Contract Arm.isa where
  pre s :=
    let state : Region := ⟨State.addr (s.gpr .r0), 200⟩
    let scratch : Region := ⟨State.addr (stackArg s 0), 640⟩
    let args : Region := ⟨stackArgAddr s 0, 4⟩
    s.rd = [args] ∧ s.wr = [state, scratch] ∧ state.Disjoint scratch ∧
    args.Disjoint state ∧ args.Disjoint scratch ∧
    (s.gpr .r0).toNat + 200 ≤ 2 ^ 32 ∧ (stackArg s 0).toNat + 640 ≤ 2 ^ 32 ∧
    s.sp.toNat + 4 ≤ 2 ^ 32 ∧
    (s.gpr .r1).toNat ∈ rates ∧ (s.gpr .r2).toNat < (s.gpr .r1).toNat
  post s s' := ∀ msg, Repr s.mem (State.addr (s.gpr .r0)) (s.gpr .r1).toNat msg →
    (s.gpr .r2).toNat = msg.length % (s.gpr .r1).toNat →
    stateAt s'.mem (State.addr (s.gpr .r0)) =
      absorb (s.gpr .r1).toNat (pad (s.gpr .r1).toNat ((s.gpr .r3).setWidth 8) msg)
  pub s₁ s₂ :=
    s₁.sp = s₂.sp ∧ s₁.gpr .r0 = s₂.gpr .r0 ∧ s₁.gpr .r1 = s₂.gpr .r1 ∧ s₁.gpr .r2 = s₂.gpr .r2 ∧
    s₁.gpr .r3 = s₂.gpr .r3 ∧ stackArg s₁ 0 = stackArg s₂ 0

open Arm in
/-- 32-bit ARM contract for `vg_keccak_squeeze(state = r0, rate = r1,
pos = r2, out = r3, outlen = [sp], scratch = [sp, #4]) -> r0`: writes
`outlen` bytes of output from byte `pos` on to `out`, and returns the
position after them, leaving a state from which the output continues.

The code may read the arguments on the stack (8 bytes at `sp`), and read
and write `state` (200 bytes), `out` (`outlen` bytes) and `scratch` (640
bytes), which may not overlap each other or the arguments, or wrap around
the end of the (32-bit) address space. `rate` is one of `rates`, and
`pos ≤ rate`. -/
def squeezeArm : Contract Arm.isa where
  pre s :=
    let state : Region := ⟨State.addr (s.gpr .r0), 200⟩
    let out : Region := ⟨State.addr (s.gpr .r3), (stackArg s 0).toNat⟩
    let scratch : Region := ⟨State.addr (stackArg s 1), 640⟩
    let args : Region := ⟨stackArgAddr s 0, 8⟩
    s.rd = [args] ∧ s.wr = [state, out, scratch] ∧
    state.Disjoint out ∧ state.Disjoint scratch ∧ out.Disjoint scratch ∧
    args.Disjoint state ∧ args.Disjoint out ∧ args.Disjoint scratch ∧
    (s.gpr .r0).toNat + 200 ≤ 2 ^ 32 ∧ (s.gpr .r3).toNat + (stackArg s 0).toNat ≤ 2 ^ 32 ∧
    (stackArg s 1).toNat + 640 ≤ 2 ^ 32 ∧ s.sp.toNat + 8 ≤ 2 ^ 32 ∧
    (s.gpr .r1).toNat ∈ rates ∧ (s.gpr .r2).toNat ≤ (s.gpr .r1).toNat
  post s s' :=
    bytesAt s'.mem (State.addr (s.gpr .r3)) (stackArg s 0).toNat =
      squeezeFrom (s.gpr .r1).toNat (stateAt s.mem (State.addr (s.gpr .r0))) (s.gpr .r2).toNat
        (stackArg s 0).toNat ∧
    (s'.gpr .r0).toNat ≤ (s.gpr .r1).toNat ∧
    ∀ d, squeezeFrom (s.gpr .r1).toNat (stateAt s'.mem (State.addr (s.gpr .r0))) (s'.gpr .r0).toNat d =
      squeezeFrom (s.gpr .r1).toNat (stateAt s.mem (State.addr (s.gpr .r0)))
        ((s.gpr .r2).toNat + (stackArg s 0).toNat) d
  pub s₁ s₂ :=
    s₁.sp = s₂.sp ∧ s₁.gpr .r0 = s₂.gpr .r0 ∧ s₁.gpr .r1 = s₂.gpr .r1 ∧ s₁.gpr .r2 = s₂.gpr .r2 ∧
    s₁.gpr .r3 = s₂.gpr .r3 ∧ stackArg s₁ 0 = stackArg s₂ 0 ∧ stackArg s₁ 1 = stackArg s₂ 1

end VG.Proof.Sha3
