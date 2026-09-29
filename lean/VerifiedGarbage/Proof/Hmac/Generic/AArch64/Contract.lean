import VerifiedGarbage.Spec.Pbkdf2.Generic
import VerifiedGarbage.TCB.AArch64.Target

/-!
# HMAC and PBKDF2-HMAC over any streaming hash function: the AArch64 contracts

**Untrusted**: the contracts the proofs are written against, as on x86-64
(`Proof/Hmac/Generic/X86_64/Contract.lean`).

* `initK`, `updK` and `finK` are the AArch64 contracts of a hash function's
  streaming `init`, `update` and `finalize`, with the sizes and the
  representation of the streaming state as parameters. Each lets the callee
  use the 16 bytes below the stack pointer (a frame saving `x30`), as SHA-1's
  and MD5's do; the contracts the functions are proved against imply them
  (the SHA-512 family's, which use no stack, too).
* `initG`, `finG` and `iterG` are those of our functions, which use no
  stack of their own but let the functions they call use those 16 bytes;
  the artifacts are emitted with the shared contracts of
  `Spec/Hmac/Generic.lean` and `Spec/Pbkdf2/Generic.lean`, which imply them
  (`Contract.Implies`).

The return address is in `x30`, not on the stack, so no region needs to be
kept disjoint from it.
-/

namespace VG.Proof.Hmac.Generic.AArch64

open VG.AArch64
open Spec.Hmac (StreamingHash xorPad ipad opad blockKey hmacBlockKey)
open Spec.Sha256 (bytesAt)

/-- The 16 bytes below the stack pointer. -/
abbrev stk (s : State) : Region := ⟨s.sp - 16, 16⟩

/-! ## The functions we call -/

/-- `init(state)`: makes the `S`-byte streaming state at `state` represent the
empty message. -/
def initK (S : Nat) (R : Mem → Addr → List Byte → Prop) : Contract isa where
  pre s := s.rd = [] ∧ s.wr = [⟨s.gpr .x0, S⟩]
  post s s' := R s'.mem (s.gpr .x0) []
  pub s₁ s₂ := s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.sp = s₂.sp

/-- `update(state, count, data, len, scratch)`, with `Wb` bytes of scratch
space. -/
def updK (S Wb : Nat) (R : Mem → Addr → List Byte → Prop) : Contract isa where
  pre s :=
    let state : Region := ⟨s.gpr .x0, S⟩
    let data : Region := ⟨s.gpr .x2, (s.gpr .x3).toNat⟩
    let scratch : Region := ⟨s.gpr .x4, Wb⟩
    s.rd = [data] ∧ s.wr = [state, scratch] ∧
    state.Disjoint scratch ∧ data.Disjoint state ∧ data.Disjoint scratch ∧
    16 ≤ s.sp.toNat ∧ (stk s).Disjoint state ∧ (stk s).Disjoint data ∧ (stk s).Disjoint scratch
  post s s' := ∀ m, R s.mem (s.gpr .x0) m → s.gpr .x1 = BitVec.ofNat 64 m.length →
    R s'.mem (s.gpr .x0) (m ++ bytesAt s.mem (s.gpr .x2) (s.gpr .x3).toNat)
  pub s₁ s₂ :=
    s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.gpr .x2 = s₂.gpr .x2 ∧
    s₁.gpr .x3 = s₂.gpr .x3 ∧ s₁.gpr .x4 = s₂.gpr .x4 ∧ s₁.sp = s₂.sp

/-- `finalize(state, count, out, scratch)`, writing `F` bytes whose first
`D` are the digest `hash m`, for a message of fewer than 2⁶⁴ bytes. -/
def finK (S Wb F D : Nat) (R : Mem → Addr → List Byte → Prop) (hash : List Byte → List Byte) :
    Contract isa where
  pre s :=
    let state : Region := ⟨s.gpr .x0, S⟩
    let out : Region := ⟨s.gpr .x2, F⟩
    let scratch : Region := ⟨s.gpr .x3, Wb⟩
    s.rd = [] ∧ s.wr = [state, out, scratch] ∧
    state.Disjoint out ∧ state.Disjoint scratch ∧ out.Disjoint scratch ∧
    16 ≤ s.sp.toNat ∧ (stk s).Disjoint state ∧ (stk s).Disjoint out ∧ (stk s).Disjoint scratch
  post s s' := ∀ m, R s.mem (s.gpr .x0) m → m.length < 2 ^ 64 →
    s.gpr .x1 = BitVec.ofNat 64 m.length → (bytesAt s'.mem (s.gpr .x2) F).take D = hash m
  pub s₁ s₂ :=
    s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.gpr .x2 = s₂.gpr .x2 ∧
    s₁.gpr .x3 = s₂.gpr .x3 ∧ s₁.sp = s₂.sp

/-! ## Our functions

`S` is a streaming hash function and `W` the number of 64-bit words of
scratch space. -/

variable (S : StreamingHash) (W : Nat)

/-- `init(inner, outer, key, key_len, scratch)`: `VG.Spec.Hmac.initContract`. -/
def initG : Contract isa where
  pre s :=
    let inner : Region := ⟨s.gpr .x0, S.stateBytes⟩
    let outer : Region := ⟨s.gpr .x1, S.stateBytes⟩
    let key : Region := ⟨s.gpr .x2, (s.gpr .x3).toNat⟩
    let scratch : Region := ⟨s.gpr .x4, 8 * W⟩
    (s.gpr .x3).toNat ≤ S.H.blockSize ∧ s.rd = [key] ∧ s.wr = [inner, outer, scratch] ∧
    inner.Disjoint outer ∧ inner.Disjoint scratch ∧ outer.Disjoint scratch ∧
    key.Disjoint inner ∧ key.Disjoint outer ∧ key.Disjoint scratch ∧
    16 ≤ s.sp.toNat ∧ (stk s).Disjoint inner ∧ (stk s).Disjoint outer ∧ (stk s).Disjoint key ∧
    (stk s).Disjoint scratch ∧ (s.gpr .x4).toNat + 8 * W ≤ 2 ^ 64
  post s s' :=
    let k0 := blockKey S.H (bytesAt s.mem (s.gpr .x2) (s.gpr .x3).toNat)
    S.Repr s'.mem (s.gpr .x0) (xorPad k0 ipad) ∧ S.Repr s'.mem (s.gpr .x1) (xorPad k0 opad)
  pub s₁ s₂ :=
    s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.gpr .x2 = s₂.gpr .x2 ∧
    s₁.gpr .x3 = s₂.gpr .x3 ∧ s₁.gpr .x4 = s₂.gpr .x4 ∧ s₁.sp = s₂.sp

/-- `finalize(inner, outer, count, out, scratch)`: `VG.Spec.Hmac.finalizeContract`. -/
def finG : Contract isa where
  pre s :=
    let inner : Region := ⟨s.gpr .x0, S.stateBytes⟩
    let outer : Region := ⟨s.gpr .x1, S.stateBytes⟩
    let out : Region := ⟨s.gpr .x3, S.digestBytes⟩
    let scratch : Region := ⟨s.gpr .x4, 8 * W⟩
    s.rd = [outer] ∧ s.wr = [inner, out, scratch] ∧
    inner.Disjoint outer ∧ inner.Disjoint out ∧ inner.Disjoint scratch ∧
    outer.Disjoint out ∧ outer.Disjoint scratch ∧ out.Disjoint scratch ∧
    16 ≤ s.sp.toNat ∧ (stk s).Disjoint inner ∧ (stk s).Disjoint outer ∧ (stk s).Disjoint out ∧
    (stk s).Disjoint scratch ∧ (s.gpr .x4).toNat + 8 * W ≤ 2 ^ 64
  post s s' := ∀ k0 text, k0.length = S.H.blockSize → k0.length + text.length < 2 ^ 64 →
    S.Repr s.mem (s.gpr .x0) (xorPad k0 ipad ++ text) →
    s.gpr .x2 = BitVec.ofNat 64 (S.H.blockSize + text.length) →
    S.Repr s.mem (s.gpr .x1) (xorPad k0 opad) →
    bytesAt s'.mem (s.gpr .x3) S.digestBytes = hmacBlockKey S.H k0 text
  pub s₁ s₂ :=
    s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.gpr .x2 = s₂.gpr .x2 ∧
    s₁.gpr .x3 = s₂.gpr .x3 ∧ s₁.gpr .x4 = s₂.gpr .x4 ∧ s₁.sp = s₂.sp

/-- `iterate(key, u, n, t, scratch)`: `VG.Spec.Pbkdf2.iterateContract`. -/
def iterG : Contract isa where
  pre s :=
    let key : Region := ⟨s.gpr .x0, 2 * S.stateBytes⟩
    let u : Region := ⟨s.gpr .x1, S.digestBytes⟩
    let t : Region := ⟨s.gpr .x3, S.digestBytes⟩
    let scratch : Region := ⟨s.gpr .x4, 8 * W⟩
    s.rd = [key, u] ∧ s.wr = [t, scratch] ∧
    key.Disjoint t ∧ key.Disjoint scratch ∧ u.Disjoint t ∧ u.Disjoint scratch ∧ t.Disjoint scratch ∧
    16 ≤ s.sp.toNat ∧ (stk s).Disjoint key ∧ (stk s).Disjoint u ∧ (stk s).Disjoint t ∧
    (stk s).Disjoint scratch ∧
    (s.gpr .x0).toNat + 2 * S.stateBytes ≤ 2 ^ 64 ∧ (s.gpr .x4).toNat + 8 * W ≤ 2 ^ 64
  post s s' := ∀ k0, k0.length = S.H.blockSize →
    S.Repr s.mem (s.gpr .x0) (xorPad k0 ipad) →
    S.Repr s.mem (s.gpr .x0 + BitVec.ofNat 64 S.stateBytes) (xorPad k0 opad) →
    bytesAt s'.mem (s.gpr .x3) S.digestBytes =
      Spec.Pbkdf2.iterate (hmacBlockKey S.H k0) ((s.gpr .x2).setWidth 32).toNat
        (bytesAt s.mem (s.gpr .x1) S.digestBytes) (bytesAt s.mem (s.gpr .x3) S.digestBytes)
  pub s₁ s₂ :=
    s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧
    (s₁.gpr .x2).setWidth 32 = (s₂.gpr .x2).setWidth 32 ∧
    s₁.gpr .x3 = s₂.gpr .x3 ∧ s₁.gpr .x4 = s₂.gpr .x4 ∧ s₁.sp = s₂.sp

end VG.Proof.Hmac.Generic.AArch64
