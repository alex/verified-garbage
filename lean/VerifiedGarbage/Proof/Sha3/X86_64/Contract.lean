import VerifiedGarbage.Spec.Sha3.Contract
import VerifiedGarbage.TCB.X86_64.Target

/-!
# SHA-3: the x86-64 contracts

**Untrusted**: the contracts the proofs are written against; the artifacts
are emitted with the shared contracts of `Spec/`, which imply these
(`Contract.Implies`).
-/

namespace VG.Proof.Sha3

open Spec.Sha3

open X86_64 in
/-- x86-64 contract for
`vg_keccak_f1600(state: *mut [u64; 25], scratch: *mut [u64; 64])`: applies
Keccak-f[1600] to the state at `state`.

The code may read and write `state` (200 bytes) and `scratch` (512 bytes,
whose contents on exit are unspecified). These may not overlap each other,
nor the return address on the stack. The pointers are public; the state is
secret. It returns with `rdi` and `rsi` as they were, which callers rely
on. -/
def permuteX86_64 : Contract X86_64.isa where
  pre s :=
    let state : Region := ⟨s.gpr .rdi, 200⟩
    let scratch : Region := ⟨s.gpr .rsi, 512⟩
    let ret : Region := ⟨s.gpr .rsp, 8⟩
    s.rd = [] ∧ s.wr = [state, scratch] ∧
    state.Disjoint scratch ∧ ret.Disjoint state ∧ ret.Disjoint scratch
  post s s' := stateAt s'.mem (s.gpr .rdi) = keccakF (stateAt s.mem (s.gpr .rdi)) ∧
    s'.gpr .rdi = s.gpr .rdi ∧ s'.gpr .rsi = s.gpr .rsi
  pub s₁ s₂ := s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi

open X86_64 in
/-- x86-64 contract for `vg_keccak_absorb(state = rdi, rate = rsi, pos = rdx,
data = rcx, len = r8, scratch = r9) -> rax`: absorbs `data` into the
streaming state (`Repr`) and returns the new position in the block.

The code may read `data`, read and write `state` (200 bytes) and `scratch`
(640 bytes), and store a return address in the 8 bytes below `rsp`, none of
which overlap each other or the return address. `rate` is one of `rates`,
and `pos < rate`. -/
def absorbX86_64 : Contract X86_64.isa where
  pre s :=
    let state : Region := ⟨s.gpr .rdi, 200⟩
    let data : Region := ⟨s.gpr .rcx, (s.gpr .r8).toNat⟩
    let scratch : Region := ⟨s.gpr .r9, 640⟩
    let ret : Region := ⟨s.gpr .rsp, 8⟩
    let stack : Region := ⟨s.gpr .rsp - 8, 8⟩
    s.rd = [data] ∧ s.wr = [state, scratch] ∧
    state.Disjoint scratch ∧ data.Disjoint state ∧ data.Disjoint scratch ∧
    ret.Disjoint state ∧ ret.Disjoint scratch ∧
    stack.Disjoint state ∧ stack.Disjoint data ∧ stack.Disjoint scratch ∧
    (s.gpr .rsi).toNat ∈ rates ∧ (s.gpr .rdx).toNat < (s.gpr .rsi).toNat
  post s s' :=
    (∀ msg, Repr s.mem (s.gpr .rdi) (s.gpr .rsi).toNat msg →
      (s.gpr .rdx).toNat = msg.length % (s.gpr .rsi).toNat →
      Repr s'.mem (s.gpr .rdi) (s.gpr .rsi).toNat
        (msg ++ bytesAt s.mem (s.gpr .rcx) (s.gpr .r8).toNat)) ∧
    (s'.gpr .rax).toNat = ((s.gpr .rdx).toNat + (s.gpr .r8).toNat) % (s.gpr .rsi).toNat
  pub s₁ s₂ :=
    s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rdx = s₂.gpr .rdx ∧
    s₁.gpr .rcx = s₂.gpr .rcx ∧ s₁.gpr .r8 = s₂.gpr .r8 ∧ s₁.gpr .r9 = s₂.gpr .r9 ∧
    s₁.gpr .rsp = s₂.gpr .rsp

open X86_64 in
/-- x86-64 contract for `vg_keccak_pad(state = rdi, rate = rsi, pos = rdx,
suffix = rcx, scratch = r8)`: absorbs the padding (with the low byte of
`suffix`) into the streaming state.

The code may read and write `state` (200 bytes) and `scratch` (640 bytes),
and store a return address in the 8 bytes below `rsp`, none of which overlap
each other or the return address. `rate` is one of `rates`, and
`pos < rate`. -/
def padX86_64 : Contract X86_64.isa where
  pre s :=
    let state : Region := ⟨s.gpr .rdi, 200⟩
    let scratch : Region := ⟨s.gpr .r8, 640⟩
    let ret : Region := ⟨s.gpr .rsp, 8⟩
    let stack : Region := ⟨s.gpr .rsp - 8, 8⟩
    s.rd = [] ∧ s.wr = [state, scratch] ∧
    state.Disjoint scratch ∧ ret.Disjoint state ∧ ret.Disjoint scratch ∧
    stack.Disjoint state ∧ stack.Disjoint scratch ∧
    (s.gpr .rsi).toNat ∈ rates ∧ (s.gpr .rdx).toNat < (s.gpr .rsi).toNat
  post s s' := ∀ msg, Repr s.mem (s.gpr .rdi) (s.gpr .rsi).toNat msg →
    (s.gpr .rdx).toNat = msg.length % (s.gpr .rsi).toNat →
    stateAt s'.mem (s.gpr .rdi) =
      absorb (s.gpr .rsi).toNat (pad (s.gpr .rsi).toNat ((s.gpr .rcx).setWidth 8) msg)
  pub s₁ s₂ :=
    s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rdx = s₂.gpr .rdx ∧
    s₁.gpr .r8 = s₂.gpr .r8 ∧ s₁.gpr .rsp = s₂.gpr .rsp

open X86_64 in
/-- x86-64 contract for `vg_keccak_squeeze(state = rdi, rate = rsi, pos = rdx,
out = rcx, outlen = r8, scratch = r9) -> rax`: writes `outlen` bytes of
output from byte `pos` on to `out`, and returns the position after them,
leaving a state from which the output continues.

The code may read and write `state` (200 bytes), `out` (`outlen` bytes) and
`scratch` (640 bytes), and store a return address in the 8 bytes below
`rsp`, none of which overlap each other or the return address. `rate` is
one of `rates`, and `pos ≤ rate`. -/
def squeezeX86_64 : Contract X86_64.isa where
  pre s :=
    let state : Region := ⟨s.gpr .rdi, 200⟩
    let out : Region := ⟨s.gpr .rcx, (s.gpr .r8).toNat⟩
    let scratch : Region := ⟨s.gpr .r9, 640⟩
    let ret : Region := ⟨s.gpr .rsp, 8⟩
    let stack : Region := ⟨s.gpr .rsp - 8, 8⟩
    s.rd = [] ∧ s.wr = [state, out, scratch] ∧
    state.Disjoint out ∧ state.Disjoint scratch ∧ out.Disjoint scratch ∧
    ret.Disjoint state ∧ ret.Disjoint out ∧ ret.Disjoint scratch ∧
    stack.Disjoint state ∧ stack.Disjoint out ∧ stack.Disjoint scratch ∧
    (s.gpr .rsi).toNat ∈ rates ∧ (s.gpr .rdx).toNat ≤ (s.gpr .rsi).toNat
  post s s' :=
    bytesAt s'.mem (s.gpr .rcx) (s.gpr .r8).toNat =
      squeezeFrom (s.gpr .rsi).toNat (stateAt s.mem (s.gpr .rdi)) (s.gpr .rdx).toNat (s.gpr .r8).toNat ∧
    (s'.gpr .rax).toNat ≤ (s.gpr .rsi).toNat ∧
    ∀ d, squeezeFrom (s.gpr .rsi).toNat (stateAt s'.mem (s.gpr .rdi)) (s'.gpr .rax).toNat d =
      squeezeFrom (s.gpr .rsi).toNat (stateAt s.mem (s.gpr .rdi))
        ((s.gpr .rdx).toNat + (s.gpr .r8).toNat) d
  pub s₁ s₂ :=
    s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rdx = s₂.gpr .rdx ∧
    s₁.gpr .rcx = s₂.gpr .rcx ∧ s₁.gpr .r8 = s₂.gpr .r8 ∧ s₁.gpr .r9 = s₂.gpr .r9 ∧
    s₁.gpr .rsp = s₂.gpr .rsp

end VG.Proof.Sha3
