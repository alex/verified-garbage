import VerifiedGarbage.Spec.Sha3.Contract
import VerifiedGarbage.TCB.X86.Target

/-!
# SHA-3: the x86 (32-bit) contracts

**Untrusted**: the contracts the proofs are written against; the artifacts
are emitted with the shared contracts of `Spec/`, which imply these
(`Contract.Implies`), with the arguments on the stack (cdecl).

The streaming functions call the permutation, each call pushing its two
arguments and storing its return address in the 12 bytes of stack below
the return address; they may overwrite their own arguments (`writeArgs`),
which the code does not do.
-/

namespace VG.Proof.Sha3

open Spec.Sha3

open X86 in
/-- x86 (32-bit) contract for
`vg_keccak_f1600(state: *mut [u64; 25], scratch: *mut [u64; 64])`: applies
Keccak-f[1600] to the state at `state`.

The code may read the arguments (8 bytes above the return address), and read
and write `state` (200 bytes) and `scratch` (512 bytes, whose contents on
exit are unspecified), which may not overlap each other, the arguments or
the return address, or wrap around the end of the (32-bit) address space.
`esp` and the pointers are public; the state is secret. -/
def permuteX86 : Contract X86.isa where
  pre s :=
    let state : Region := ⟨(arg s 0).setWidth 64, 200⟩
    let scratch : Region := ⟨(arg s 1).setWidth 64, 512⟩
    let args : Region := ⟨argAddr s 0, 8⟩
    let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
    s.rd = [args] ∧ s.wr = [state, scratch] ∧
    state.Disjoint scratch ∧ args.Disjoint state ∧ args.Disjoint scratch ∧
    ret.Disjoint state ∧ ret.Disjoint scratch ∧
    (arg s 0).toNat + 200 ≤ 2 ^ 32 ∧ (arg s 1).toNat + 512 ≤ 2 ^ 32 ∧ (s.gpr .esp).toNat + 12 ≤ 2 ^ 32
  post s s' :=
    stateAt s'.mem ((arg s 0).setWidth 64) = keccakF (stateAt s.mem ((arg s 0).setWidth 64))
  pub s₁ s₂ := s₁.gpr .esp = s₂.gpr .esp ∧ arg s₁ 0 = arg s₂ 0 ∧ arg s₁ 1 = arg s₂ 1

open X86 in
/-- x86 (32-bit) contract for `vg_keccak_absorb(state, rate, pos, data, len,
scratch) -> eax`, whose arguments are on the stack: absorbs `data` into the
streaming state (`Repr`) and returns the new position in the block.

The code may read `data` (`len` bytes), and read and write `state` (200
bytes), `scratch` (640 bytes) and the arguments (24 bytes above the return
address). None of these may overlap another; none of the buffers may
overlap the return address or the 12 bytes of stack below it; nothing may
wrap around the end of the (32-bit) address space. `rate` is one of
`rates`, and `pos < rate`. `esp` and the arguments are public; the state and
the data are secret. -/
def absorbX86 : Contract X86.isa where
  pre s :=
    let state : Region := ⟨(arg s 0).setWidth 64, 200⟩
    let data : Region := ⟨(arg s 3).setWidth 64, (arg s 4).toNat⟩
    let scratch : Region := ⟨(arg s 5).setWidth 64, 640⟩
    let args : Region := ⟨argAddr s 0, 24⟩
    let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
    let stack : Region := ⟨(s.gpr .esp).setWidth 64 - 12, 12⟩
    s.rd = [data] ∧ s.wr = [state, scratch, args] ∧
    state.Disjoint scratch ∧ data.Disjoint state ∧ data.Disjoint scratch ∧
    args.Disjoint state ∧ args.Disjoint data ∧ args.Disjoint scratch ∧
    ret.Disjoint state ∧ ret.Disjoint data ∧ ret.Disjoint scratch ∧
    stack.Disjoint state ∧ stack.Disjoint data ∧ stack.Disjoint scratch ∧
    (arg s 0).toNat + 200 ≤ 2 ^ 32 ∧ (arg s 3).toNat + (arg s 4).toNat ≤ 2 ^ 32 ∧
    (arg s 5).toNat + 640 ≤ 2 ^ 32 ∧ 12 ≤ (s.gpr .esp).toNat ∧ (s.gpr .esp).toNat + 28 ≤ 2 ^ 32 ∧
    (arg s 1).toNat ∈ rates ∧ (arg s 2).toNat < (arg s 1).toNat
  post s s' :=
    (∀ msg, Repr s.mem ((arg s 0).setWidth 64) (arg s 1).toNat msg →
      (arg s 2).toNat = msg.length % (arg s 1).toNat →
      Repr s'.mem ((arg s 0).setWidth 64) (arg s 1).toNat
        (msg ++ bytesAt s.mem ((arg s 3).setWidth 64) (arg s 4).toNat)) ∧
    (s'.gpr .eax).toNat = ((arg s 2).toNat + (arg s 4).toNat) % (arg s 1).toNat
  pub s₁ s₂ := s₁.gpr .esp = s₂.gpr .esp ∧ ∀ i < 6, arg s₁ i = arg s₂ i

open X86 in
/-- x86 (32-bit) contract for `vg_keccak_pad(state, rate, pos, suffix,
scratch)`, whose arguments are on the stack: absorbs the padding (with the
low byte of `suffix`) into the streaming state.

The code may read and write `state` (200 bytes), `scratch` (640 bytes) and
the arguments (20 bytes above the return address). None of these may
overlap another; neither buffer may overlap the return address or the 12
bytes of stack below it; nothing may wrap around the end of the (32-bit)
address space. `rate` is one of `rates`, and `pos < rate`. `esp` and the
arguments are public; the state is secret. -/
def padX86 : Contract X86.isa where
  pre s :=
    let state : Region := ⟨(arg s 0).setWidth 64, 200⟩
    let scratch : Region := ⟨(arg s 4).setWidth 64, 640⟩
    let args : Region := ⟨argAddr s 0, 20⟩
    let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
    let stack : Region := ⟨(s.gpr .esp).setWidth 64 - 12, 12⟩
    s.rd = [] ∧ s.wr = [state, scratch, args] ∧
    state.Disjoint scratch ∧ args.Disjoint state ∧ args.Disjoint scratch ∧
    ret.Disjoint state ∧ ret.Disjoint scratch ∧ stack.Disjoint state ∧ stack.Disjoint scratch ∧
    (arg s 0).toNat + 200 ≤ 2 ^ 32 ∧ (arg s 4).toNat + 640 ≤ 2 ^ 32 ∧ 12 ≤ (s.gpr .esp).toNat ∧
    (s.gpr .esp).toNat + 24 ≤ 2 ^ 32 ∧
    (arg s 1).toNat ∈ rates ∧ (arg s 2).toNat < (arg s 1).toNat
  post s s' := ∀ msg, Repr s.mem ((arg s 0).setWidth 64) (arg s 1).toNat msg →
    (arg s 2).toNat = msg.length % (arg s 1).toNat →
    stateAt s'.mem ((arg s 0).setWidth 64) =
      absorb (arg s 1).toNat (pad (arg s 1).toNat ((arg s 3).setWidth 8) msg)
  pub s₁ s₂ := s₁.gpr .esp = s₂.gpr .esp ∧ ∀ i < 5, arg s₁ i = arg s₂ i

open X86 in
/-- x86 (32-bit) contract for `vg_keccak_squeeze(state, rate, pos, out,
outlen, scratch) -> eax`, whose arguments are on the stack: writes `outlen`
bytes of output from byte `pos` on to `out`, and returns the position after
them, leaving a state from which the output continues.

The code may read and write `state` (200 bytes), `out` (`outlen` bytes),
`scratch` (640 bytes) and the arguments (24 bytes above the return address).
None of these may overlap another; none of the buffers may overlap the
return address or the 12 bytes of stack below it; nothing may wrap around
the end of the (32-bit) address space. `rate` is one of `rates`, and
`pos ≤ rate`. `esp` and the arguments are public; the state is secret. -/
def squeezeX86 : Contract X86.isa where
  pre s :=
    let state : Region := ⟨(arg s 0).setWidth 64, 200⟩
    let out : Region := ⟨(arg s 3).setWidth 64, (arg s 4).toNat⟩
    let scratch : Region := ⟨(arg s 5).setWidth 64, 640⟩
    let args : Region := ⟨argAddr s 0, 24⟩
    let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
    let stack : Region := ⟨(s.gpr .esp).setWidth 64 - 12, 12⟩
    s.rd = [] ∧ s.wr = [state, out, scratch, args] ∧
    state.Disjoint out ∧ state.Disjoint scratch ∧ out.Disjoint scratch ∧
    args.Disjoint state ∧ args.Disjoint out ∧ args.Disjoint scratch ∧
    ret.Disjoint state ∧ ret.Disjoint out ∧ ret.Disjoint scratch ∧
    stack.Disjoint state ∧ stack.Disjoint out ∧ stack.Disjoint scratch ∧
    (arg s 0).toNat + 200 ≤ 2 ^ 32 ∧ (arg s 3).toNat + (arg s 4).toNat ≤ 2 ^ 32 ∧
    (arg s 5).toNat + 640 ≤ 2 ^ 32 ∧ 12 ≤ (s.gpr .esp).toNat ∧ (s.gpr .esp).toNat + 28 ≤ 2 ^ 32 ∧
    (arg s 1).toNat ∈ rates ∧ (arg s 2).toNat ≤ (arg s 1).toNat
  post s s' :=
    bytesAt s'.mem ((arg s 3).setWidth 64) (arg s 4).toNat =
      squeezeFrom (arg s 1).toNat (stateAt s.mem ((arg s 0).setWidth 64)) (arg s 2).toNat
        (arg s 4).toNat ∧
    (s'.gpr .eax).toNat ≤ (arg s 1).toNat ∧
    ∀ d, squeezeFrom (arg s 1).toNat (stateAt s'.mem ((arg s 0).setWidth 64)) (s'.gpr .eax).toNat d =
      squeezeFrom (arg s 1).toNat (stateAt s.mem ((arg s 0).setWidth 64))
        ((arg s 2).toNat + (arg s 4).toNat) d
  pub s₁ s₂ := s₁.gpr .esp = s₂.gpr .esp ∧ ∀ i < 6, arg s₁ i = arg s₂ i

end VG.Proof.Sha3
