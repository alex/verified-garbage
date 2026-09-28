import VerifiedGarbage.Spec.Sha3.Contract
import VerifiedGarbage.TCB.AArch64.Target

/-!
# SHA-3: the AArch64 contracts

**Untrusted**: the contracts the proofs are written against; the artifacts
are emitted with the shared contracts of `Spec/`, which imply these
(`Contract.Implies`).

The return address is in the link register `x30`, which the target's
calling convention requires to be preserved (`VG.AArch64.abiPreserved`), not
on the stack, so unlike on x86-64 no region needs to be kept disjoint from
it. The streaming functions save `x30` in a frame of 16 bytes below the
stack pointer around their calls of the permutation.
-/

namespace VG.Proof.Sha3

open Spec.Sha3

open AArch64 in
/-- AArch64 contract for
`vg_keccak_f1600(state: *mut [u64; 25], scratch: *mut [u64; 64])`: applies
Keccak-f[1600] to the state at `state`.

The code may read and write `state` (200 bytes) and `scratch` (512 bytes,
whose contents on exit are unspecified), which may not overlap. The pointers
are public; the state is secret. -/
def permuteAArch64 : Contract AArch64.isa where
  pre s :=
    let state : Region := ⟨s.gpr .x0, 200⟩
    let scratch : Region := ⟨s.gpr .x1, 512⟩
    s.rd = [] ∧ s.wr = [state, scratch] ∧ state.Disjoint scratch
  post s s' := stateAt s'.mem (s.gpr .x0) = keccakF (stateAt s.mem (s.gpr .x0))
  pub s₁ s₂ := s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.sp = s₂.sp

open AArch64 in
/-- AArch64 contract for `vg_keccak_absorb(state = x0, rate = x1, pos = x2,
data = x3, len = x4, scratch = x5) -> x0`: absorbs `data` into the streaming
state (`Repr`) and returns the new position in the block.

The code may read `data`, and read and write `state` (200 bytes) and
`scratch` (640 bytes), none of which overlap each other or the 16 bytes
below the stack pointer (the frame saving `x30`), which do not wrap around.
`rate` is one of `rates`, and `pos < rate`. -/
def absorbAArch64 : Contract AArch64.isa where
  pre s :=
    let state : Region := ⟨s.gpr .x0, 200⟩
    let data : Region := ⟨s.gpr .x3, (s.gpr .x4).toNat⟩
    let scratch : Region := ⟨s.gpr .x5, 640⟩
    let stack : Region := ⟨s.sp - 16, 16⟩
    s.rd = [data] ∧ s.wr = [state, scratch] ∧
    state.Disjoint scratch ∧ data.Disjoint state ∧ data.Disjoint scratch ∧
    16 ≤ s.sp.toNat ∧ stack.Disjoint state ∧ stack.Disjoint data ∧ stack.Disjoint scratch ∧
    (s.gpr .x1).toNat ∈ rates ∧ (s.gpr .x2).toNat < (s.gpr .x1).toNat
  post s s' :=
    (∀ msg, Repr s.mem (s.gpr .x0) (s.gpr .x1).toNat msg →
      (s.gpr .x2).toNat = msg.length % (s.gpr .x1).toNat →
      Repr s'.mem (s.gpr .x0) (s.gpr .x1).toNat
        (msg ++ bytesAt s.mem (s.gpr .x3) (s.gpr .x4).toNat)) ∧
    (s'.gpr .x0).toNat = ((s.gpr .x2).toNat + (s.gpr .x4).toNat) % (s.gpr .x1).toNat
  pub s₁ s₂ :=
    s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.gpr .x2 = s₂.gpr .x2 ∧
    s₁.gpr .x3 = s₂.gpr .x3 ∧ s₁.gpr .x4 = s₂.gpr .x4 ∧ s₁.gpr .x5 = s₂.gpr .x5 ∧
    s₁.sp = s₂.sp

open AArch64 in
/-- AArch64 contract for `vg_keccak_pad(state = x0, rate = x1, pos = x2,
suffix = x3, scratch = x4)`: absorbs the padding (with the low byte of
`suffix`) into the streaming state.

The code may read and write `state` (200 bytes) and `scratch` (640 bytes),
none of which overlap each other or the 16 bytes below the stack pointer
(the frame saving `x30`), which do not wrap around. `rate` is one of
`rates`, and `pos < rate`. -/
def padAArch64 : Contract AArch64.isa where
  pre s :=
    let state : Region := ⟨s.gpr .x0, 200⟩
    let scratch : Region := ⟨s.gpr .x4, 640⟩
    let stack : Region := ⟨s.sp - 16, 16⟩
    s.rd = [] ∧ s.wr = [state, scratch] ∧ state.Disjoint scratch ∧
    16 ≤ s.sp.toNat ∧ stack.Disjoint state ∧ stack.Disjoint scratch ∧
    (s.gpr .x1).toNat ∈ rates ∧ (s.gpr .x2).toNat < (s.gpr .x1).toNat
  post s s' := ∀ msg, Repr s.mem (s.gpr .x0) (s.gpr .x1).toNat msg →
    (s.gpr .x2).toNat = msg.length % (s.gpr .x1).toNat →
    stateAt s'.mem (s.gpr .x0) =
      absorb (s.gpr .x1).toNat (pad (s.gpr .x1).toNat ((s.gpr .x3).setWidth 8) msg)
  pub s₁ s₂ :=
    s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.gpr .x2 = s₂.gpr .x2 ∧
    s₁.gpr .x4 = s₂.gpr .x4 ∧ s₁.sp = s₂.sp

open AArch64 in
/-- AArch64 contract for `vg_keccak_squeeze(state = x0, rate = x1, pos = x2,
out = x3, outlen = x4, scratch = x5) -> x0`: writes `outlen` bytes of output
from byte `pos` on to `out`, and returns the position after them, leaving a
state from which the output continues.

The code may read and write `state` (200 bytes), `out` (`outlen` bytes) and
`scratch` (640 bytes), none of which overlap each other or the 16 bytes
below the stack pointer (the frame saving `x30`), which do not wrap around.
`rate` is one of `rates`, and `pos ≤ rate`. -/
def squeezeAArch64 : Contract AArch64.isa where
  pre s :=
    let state : Region := ⟨s.gpr .x0, 200⟩
    let out : Region := ⟨s.gpr .x3, (s.gpr .x4).toNat⟩
    let scratch : Region := ⟨s.gpr .x5, 640⟩
    let stack : Region := ⟨s.sp - 16, 16⟩
    s.rd = [] ∧ s.wr = [state, out, scratch] ∧
    state.Disjoint out ∧ state.Disjoint scratch ∧ out.Disjoint scratch ∧
    16 ≤ s.sp.toNat ∧ stack.Disjoint state ∧ stack.Disjoint out ∧ stack.Disjoint scratch ∧
    (s.gpr .x1).toNat ∈ rates ∧ (s.gpr .x2).toNat ≤ (s.gpr .x1).toNat
  post s s' :=
    bytesAt s'.mem (s.gpr .x3) (s.gpr .x4).toNat =
      squeezeFrom (s.gpr .x1).toNat (stateAt s.mem (s.gpr .x0)) (s.gpr .x2).toNat (s.gpr .x4).toNat ∧
    (s'.gpr .x0).toNat ≤ (s.gpr .x1).toNat ∧
    ∀ d, squeezeFrom (s.gpr .x1).toNat (stateAt s'.mem (s.gpr .x0)) (s'.gpr .x0).toNat d =
      squeezeFrom (s.gpr .x1).toNat (stateAt s.mem (s.gpr .x0))
        ((s.gpr .x2).toNat + (s.gpr .x4).toNat) d
  pub s₁ s₂ :=
    s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.gpr .x2 = s₂.gpr .x2 ∧
    s₁.gpr .x3 = s₂.gpr .x3 ∧ s₁.gpr .x4 = s₂.gpr .x4 ∧ s₁.gpr .x5 = s₂.gpr .x5 ∧
    s₁.sp = s₂.sp

end VG.Proof.Sha3
