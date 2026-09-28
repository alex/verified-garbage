import VerifiedGarbage.Spec.Pbkdf2.Generic
import VerifiedGarbage.TCB.X86_64.Target

/-!
# HMAC and PBKDF2-HMAC over any streaming hash function: the x86-64 contracts

**Untrusted**: the contracts the proofs are written against.

* `initK`, `updK` and `finK` are the x86-64 contracts of a hash function's
  streaming `init`, `update` and `finalize`, with the sizes and the
  representation of the streaming state as parameters. At SHA-1 and MD5
  they are the contracts those functions are proved against
  (`Proof/<Alg>/X86_64/Contract.lean`); the SHA-512 family's imply them.
* `initG`, `finG` and `iterG` are those of our functions; the artifacts are
  emitted with the shared contracts of `Spec/Hmac/Generic.lean` and
  `Spec/Pbkdf2/Generic.lean`, which imply them (`Contract.Implies`).
-/

namespace VG.Proof.Hmac.Generic.X86_64

open VG.X86_64
open Spec.Hmac (StreamingHash xorPad ipad opad blockKey hmacBlockKey)
open Spec.Sha256 (bytesAt)

/-! ## The functions we call -/

/-- `init(state)`: makes the `S`-byte streaming state at `state` represent the
empty message. -/
def initK (S : Nat) (R : Mem → Addr → List Byte → Prop) : Contract isa where
  pre s :=
    let state : Region := ⟨s.gpr .rdi, S⟩
    let ret : Region := ⟨s.gpr .rsp, 8⟩
    s.rd = [] ∧ s.wr = [state] ∧ ret.Disjoint state
  post s s' := R s'.mem (s.gpr .rdi) []
  pub s₁ s₂ := s₁.gpr .rdi = s₂.gpr .rdi

/-- `update(state, count, data, len, scratch)`, with `Wb` bytes of scratch
space and one call below it. -/
def updK (S Wb : Nat) (R : Mem → Addr → List Byte → Prop) : Contract isa where
  pre s :=
    let state : Region := ⟨s.gpr .rdi, S⟩
    let data : Region := ⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩
    let scratch : Region := ⟨s.gpr .r8, Wb⟩
    let ret : Region := ⟨s.gpr .rsp, 8⟩
    let stack : Region := ⟨s.gpr .rsp - 8, 8⟩
    s.rd = [data] ∧ s.wr = [state, scratch] ∧
    state.Disjoint scratch ∧ data.Disjoint state ∧ data.Disjoint scratch ∧
    ret.Disjoint state ∧ ret.Disjoint scratch ∧
    stack.Disjoint state ∧ stack.Disjoint data ∧ stack.Disjoint scratch
  post s s' := ∀ m, R s.mem (s.gpr .rdi) m → s.gpr .rsi = BitVec.ofNat 64 m.length →
    R s'.mem (s.gpr .rdi) (m ++ bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat)
  pub s₁ s₂ :=
    s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rdx = s₂.gpr .rdx ∧
    s₁.gpr .rcx = s₂.gpr .rcx ∧ s₁.gpr .r8 = s₂.gpr .r8 ∧ s₁.gpr .rsp = s₂.gpr .rsp

/-- `finalize(state, count, out, scratch)`, writing `F` bytes whose first
`D` are the digest `hash m`, for a message of fewer than 2⁶⁴ bytes. -/
def finK (S Wb F D : Nat) (R : Mem → Addr → List Byte → Prop) (hash : List Byte → List Byte) :
    Contract isa where
  pre s :=
    let state : Region := ⟨s.gpr .rdi, S⟩
    let out : Region := ⟨s.gpr .rdx, F⟩
    let scratch : Region := ⟨s.gpr .rcx, Wb⟩
    let ret : Region := ⟨s.gpr .rsp, 8⟩
    let stack : Region := ⟨s.gpr .rsp - 8, 8⟩
    s.rd = [] ∧ s.wr = [state, out, scratch] ∧
    state.Disjoint out ∧ state.Disjoint scratch ∧ out.Disjoint scratch ∧
    ret.Disjoint state ∧ ret.Disjoint out ∧ ret.Disjoint scratch ∧
    stack.Disjoint state ∧ stack.Disjoint out ∧ stack.Disjoint scratch
  post s s' := ∀ m, R s.mem (s.gpr .rdi) m → m.length < 2 ^ 64 →
    s.gpr .rsi = BitVec.ofNat 64 m.length → (bytesAt s'.mem (s.gpr .rdx) F).take D = hash m
  pub s₁ s₂ :=
    s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rdx = s₂.gpr .rdx ∧
    s₁.gpr .rcx = s₂.gpr .rcx ∧ s₁.gpr .rsp = s₂.gpr .rsp

/-! ## Our functions

`S` is a streaming hash function and `W` the number of 64-bit words of
scratch space. Each function calls functions that call functions, so it
uses the 16 bytes of stack below its return address. -/

variable (S : StreamingHash) (W : Nat)

/-- `init(inner, outer, key, key_len, scratch)`: `VG.Spec.Hmac.initContract`. -/
def initG : Contract isa where
  pre s :=
    let inner : Region := ⟨s.gpr .rdi, S.stateBytes⟩
    let outer : Region := ⟨s.gpr .rsi, S.stateBytes⟩
    let key : Region := ⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩
    let scratch : Region := ⟨s.gpr .r8, 8 * W⟩
    let ret : Region := ⟨s.gpr .rsp, 8⟩
    let stack : Region := ⟨s.gpr .rsp - 16, 16⟩
    (s.gpr .rcx).toNat ≤ S.H.blockSize ∧ s.rd = [key] ∧ s.wr = [inner, outer, scratch] ∧
    inner.Disjoint outer ∧ inner.Disjoint scratch ∧ outer.Disjoint scratch ∧
    key.Disjoint inner ∧ key.Disjoint outer ∧ key.Disjoint scratch ∧
    ret.Disjoint inner ∧ ret.Disjoint outer ∧ ret.Disjoint scratch ∧
    stack.Disjoint inner ∧ stack.Disjoint outer ∧ stack.Disjoint key ∧ stack.Disjoint scratch ∧
    (s.gpr .r8).toNat + 8 * W ≤ 2 ^ 64
  post s s' :=
    let k0 := blockKey S.H (bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat)
    S.Repr s'.mem (s.gpr .rdi) (xorPad k0 ipad) ∧ S.Repr s'.mem (s.gpr .rsi) (xorPad k0 opad)
  pub s₁ s₂ :=
    s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rdx = s₂.gpr .rdx ∧
    s₁.gpr .rcx = s₂.gpr .rcx ∧ s₁.gpr .r8 = s₂.gpr .r8 ∧ s₁.gpr .rsp = s₂.gpr .rsp

/-- `finalize(inner, outer, count, out, scratch)`: `VG.Spec.Hmac.finalizeContract`. -/
def finG : Contract isa where
  pre s :=
    let inner : Region := ⟨s.gpr .rdi, S.stateBytes⟩
    let outer : Region := ⟨s.gpr .rsi, S.stateBytes⟩
    let out : Region := ⟨s.gpr .rcx, S.digestBytes⟩
    let scratch : Region := ⟨s.gpr .r8, 8 * W⟩
    let ret : Region := ⟨s.gpr .rsp, 8⟩
    let stack : Region := ⟨s.gpr .rsp - 16, 16⟩
    s.rd = [outer] ∧ s.wr = [inner, out, scratch] ∧
    inner.Disjoint outer ∧ inner.Disjoint out ∧ inner.Disjoint scratch ∧
    outer.Disjoint out ∧ outer.Disjoint scratch ∧ out.Disjoint scratch ∧
    ret.Disjoint inner ∧ ret.Disjoint outer ∧ ret.Disjoint out ∧ ret.Disjoint scratch ∧
    stack.Disjoint inner ∧ stack.Disjoint outer ∧ stack.Disjoint out ∧ stack.Disjoint scratch ∧
    (s.gpr .r8).toNat + 8 * W ≤ 2 ^ 64
  post s s' := ∀ k0 text, k0.length = S.H.blockSize → k0.length + text.length < 2 ^ 64 →
    S.Repr s.mem (s.gpr .rdi) (xorPad k0 ipad ++ text) →
    s.gpr .rdx = BitVec.ofNat 64 (S.H.blockSize + text.length) →
    S.Repr s.mem (s.gpr .rsi) (xorPad k0 opad) →
    bytesAt s'.mem (s.gpr .rcx) S.digestBytes = hmacBlockKey S.H k0 text
  pub s₁ s₂ :=
    s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rdx = s₂.gpr .rdx ∧
    s₁.gpr .rcx = s₂.gpr .rcx ∧ s₁.gpr .r8 = s₂.gpr .r8 ∧ s₁.gpr .rsp = s₂.gpr .rsp

/-- `iterate(key, u, n, t, scratch)`: `VG.Spec.Pbkdf2.iterateContract`. -/
def iterG : Contract isa where
  pre s :=
    let key : Region := ⟨s.gpr .rdi, 2 * S.stateBytes⟩
    let u : Region := ⟨s.gpr .rsi, S.digestBytes⟩
    let t : Region := ⟨s.gpr .rcx, S.digestBytes⟩
    let scratch : Region := ⟨s.gpr .r8, 8 * W⟩
    let ret : Region := ⟨s.gpr .rsp, 8⟩
    let stack : Region := ⟨s.gpr .rsp - 16, 16⟩
    s.rd = [key, u] ∧ s.wr = [t, scratch] ∧
    key.Disjoint t ∧ key.Disjoint scratch ∧ u.Disjoint t ∧ u.Disjoint scratch ∧ t.Disjoint scratch ∧
    ret.Disjoint key ∧ ret.Disjoint u ∧ ret.Disjoint t ∧ ret.Disjoint scratch ∧
    stack.Disjoint key ∧ stack.Disjoint u ∧ stack.Disjoint t ∧ stack.Disjoint scratch ∧
    (s.gpr .rdi).toNat + 2 * S.stateBytes ≤ 2 ^ 64 ∧ (s.gpr .r8).toNat + 8 * W ≤ 2 ^ 64
  post s s' := ∀ k0, k0.length = S.H.blockSize →
    S.Repr s.mem (s.gpr .rdi) (xorPad k0 ipad) →
    S.Repr s.mem (s.gpr .rdi + BitVec.ofNat 64 S.stateBytes) (xorPad k0 opad) →
    bytesAt s'.mem (s.gpr .rcx) S.digestBytes =
      Spec.Pbkdf2.iterate (hmacBlockKey S.H k0) ((s.gpr .rdx).setWidth 32).toNat
        (bytesAt s.mem (s.gpr .rsi) S.digestBytes) (bytesAt s.mem (s.gpr .rcx) S.digestBytes)
  pub s₁ s₂ :=
    s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧
    (s₁.gpr .rdx).setWidth 32 = (s₂.gpr .rdx).setWidth 32 ∧
    s₁.gpr .rcx = s₂.gpr .rcx ∧ s₁.gpr .r8 = s₂.gpr .r8 ∧ s₁.gpr .rsp = s₂.gpr .rsp

end VG.Proof.Hmac.Generic.X86_64
