import VerifiedGarbage.Spec.Pbkdf2.Generic
import VerifiedGarbage.TCB.X86.Target

/-!
# HMAC and PBKDF2-HMAC over any streaming hash function: the x86 contracts

The contracts the proofs are written against, as on the other targets
(`Proof/Hmac/Generic/Arm/Hash.lean`). Every argument is on the stack (cdecl).

* `initK`, `updK` and `finK` are the x86 contracts of a hash function's
  streaming `init`, `update` and `finalize` (`Proof.Sha512.initX86` and the
  others), with the sizes and the representation of the streaming state as
  parameters. `update` and `finalize` use the 20 bytes of stack below their
  return address. `finalize` may write its arguments, as MD5's and SHA-1's
  do (`Proof.Md5.finalizeX86`); one that only reads them (`finKr`, as
  SHA-512's) is verified against `finK` too (`finK_of_finKr`).
* `initG`, `finG` and `iterG` are those of our functions, which use 48
  bytes of stack (a frame of up to six arguments, a return address and the
  20 bytes `update` and `finalize` use), which no buffer overlaps; they may
  only read their arguments. `initW`, `finW` and `iterW` are the same with
  the arguments writable, as the shared contracts of
  `Spec/Hmac/Generic.lean` and `Spec/Pbkdf2/Generic.lean` (which the
  artifacts are emitted with, and which imply them: `Contract.Implies`) have
  them.
-/

namespace VG.Proof.Hmac.Generic.X86

open VG.X86
open Spec.Hmac (StreamingHash xorPad ipad opad blockKey hmacBlockKey)
open Spec.Sha256 (bytesAt)

/-- The 64-bit `count` argument of `update` and `finalize`, in argument
slots 1 and 2 (cdecl: the low word first). -/
def count (s : State) : BitVec 64 := arg s 2 ++ arg s 1

/-- The 64-bit `count` argument of our `finalize`, in argument slots 2 and 3. -/
def countF (s : State) : BitVec 64 := arg s 3 ++ arg s 2

/-! ## The functions we call -/

/-- `init(state)`: makes the `S`-byte streaming state at `state` represent the
empty message. -/
def initK (S : Nat) (R : Mem → Addr → List Byte → Prop) : Contract isa where
  pre s :=
    let state : Region := ⟨(arg s 0).setWidth 64, S⟩
    let args : Region := ⟨argAddr s 0, 4⟩
    let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
    s.rd = [args] ∧ s.wr = [state] ∧ args.Disjoint state ∧ ret.Disjoint state ∧
    (arg s 0).toNat + S ≤ 2 ^ 32 ∧ (s.gpr .esp).toNat + 8 ≤ 2 ^ 32
  post s s' := R s'.mem ((arg s 0).setWidth 64) []
  pub s₁ s₂ := s₁.gpr .esp = s₂.gpr .esp ∧ arg s₁ 0 = arg s₂ 0

/-- `update(state, count, data, len, scratch)`, with `Wb` bytes of scratch
space. -/
def updK (S Wb : Nat) (R : Mem → Addr → List Byte → Prop) : Contract isa where
  pre s :=
    let state : Region := ⟨(arg s 0).setWidth 64, S⟩
    let data : Region := ⟨(arg s 3).setWidth 64, (arg s 4).toNat⟩
    let scratch : Region := ⟨(arg s 5).setWidth 64, Wb⟩
    let args : Region := ⟨argAddr s 0, 24⟩
    let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
    let stack : Region := ⟨(s.gpr .esp).setWidth 64 - 20, 20⟩
    s.rd = [data, args] ∧ s.wr = [state, scratch] ∧
    state.Disjoint scratch ∧ data.Disjoint state ∧ data.Disjoint scratch ∧
    args.Disjoint state ∧ args.Disjoint scratch ∧
    ret.Disjoint state ∧ ret.Disjoint scratch ∧ stack.Disjoint state ∧ stack.Disjoint scratch ∧
    stack.Disjoint data ∧
    (arg s 0).toNat + S ≤ 2 ^ 32 ∧ (arg s 3).toNat + (arg s 4).toNat ≤ 2 ^ 32 ∧
    (arg s 5).toNat + Wb ≤ 2 ^ 32 ∧ 20 ≤ (s.gpr .esp).toNat ∧ (s.gpr .esp).toNat + 28 ≤ 2 ^ 32
  post s s' := ∀ m, R s.mem ((arg s 0).setWidth 64) m → count s = BitVec.ofNat 64 m.length →
    R s'.mem ((arg s 0).setWidth 64) (m ++ bytesAt s.mem ((arg s 3).setWidth 64) (arg s 4).toNat)
  pub s₁ s₂ := s₁.gpr .esp = s₂.gpr .esp ∧ ∀ i < 6, arg s₁ i = arg s₂ i

/-- `finalize(state, count, out, scratch)`, writing `F` bytes whose first
`D` are the digest `hash m`, for a message of fewer than 2⁶⁴ bytes. It may
write its arguments. -/
def finK (S Wb F D : Nat) (R : Mem → Addr → List Byte → Prop) (hash : List Byte → List Byte) :
    Contract isa where
  pre s :=
    let state : Region := ⟨(arg s 0).setWidth 64, S⟩
    let out : Region := ⟨(arg s 3).setWidth 64, F⟩
    let scratch : Region := ⟨(arg s 4).setWidth 64, Wb⟩
    let args : Region := ⟨argAddr s 0, 20⟩
    let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
    let stack : Region := ⟨(s.gpr .esp).setWidth 64 - 20, 20⟩
    s.rd = [] ∧ s.wr = [state, out, scratch, args] ∧
    state.Disjoint out ∧ state.Disjoint scratch ∧ out.Disjoint scratch ∧
    args.Disjoint state ∧ args.Disjoint out ∧ args.Disjoint scratch ∧
    ret.Disjoint state ∧ ret.Disjoint out ∧ ret.Disjoint scratch ∧
    stack.Disjoint state ∧ stack.Disjoint out ∧ stack.Disjoint scratch ∧
    (arg s 0).toNat + S ≤ 2 ^ 32 ∧ (arg s 3).toNat + F ≤ 2 ^ 32 ∧
    (arg s 4).toNat + Wb ≤ 2 ^ 32 ∧ 20 ≤ (s.gpr .esp).toNat ∧ (s.gpr .esp).toNat + 24 ≤ 2 ^ 32
  post s s' := ∀ m, R s.mem ((arg s 0).setWidth 64) m → m.length < 2 ^ 64 →
    count s = BitVec.ofNat 64 m.length → (bytesAt s'.mem ((arg s 3).setWidth 64) F).take D = hash m
  pub s₁ s₂ := s₁.gpr .esp = s₂.gpr .esp ∧ ∀ i < 5, arg s₁ i = arg s₂ i

/-- `finalize(state, count, out, scratch)`, writing `F` bytes whose first
`D` are the digest `hash m`, for a message of fewer than 2⁶⁴ bytes: `finK`,
but only reading its arguments. -/
def finKr (S Wb F D : Nat) (R : Mem → Addr → List Byte → Prop) (hash : List Byte → List Byte) :
    Contract isa where
  pre s :=
    let state : Region := ⟨(arg s 0).setWidth 64, S⟩
    let out : Region := ⟨(arg s 3).setWidth 64, F⟩
    let scratch : Region := ⟨(arg s 4).setWidth 64, Wb⟩
    let args : Region := ⟨argAddr s 0, 20⟩
    let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
    let stack : Region := ⟨(s.gpr .esp).setWidth 64 - 20, 20⟩
    s.rd = [args] ∧ s.wr = [state, out, scratch] ∧
    state.Disjoint out ∧ state.Disjoint scratch ∧ out.Disjoint scratch ∧
    args.Disjoint state ∧ args.Disjoint out ∧ args.Disjoint scratch ∧
    ret.Disjoint state ∧ ret.Disjoint out ∧ ret.Disjoint scratch ∧
    stack.Disjoint state ∧ stack.Disjoint out ∧ stack.Disjoint scratch ∧
    (arg s 0).toNat + S ≤ 2 ^ 32 ∧ (arg s 3).toNat + F ≤ 2 ^ 32 ∧
    (arg s 4).toNat + Wb ≤ 2 ^ 32 ∧ 20 ≤ (s.gpr .esp).toNat ∧ (s.gpr .esp).toNat + 24 ≤ 2 ^ 32
  post s s' := ∀ m, R s.mem ((arg s 0).setWidth 64) m → m.length < 2 ^ 64 →
    count s = BitVec.ofNat 64 m.length → (bytesAt s'.mem ((arg s 3).setWidth 64) F).take D = hash m
  pub s₁ s₂ := s₁.gpr .esp = s₂.gpr .esp ∧ ∀ i < 5, arg s₁ i = arg s₂ i

/-! ## Our functions

`S` is a streaming hash function and `W` the number of 64-bit words of
scratch space. -/

variable (S : StreamingHash) (W : Nat)

/-- `init(inner, outer, key, key_len, scratch)`: `VG.Spec.Hmac.initContract`,
reading its arguments only. -/
def initG : Contract isa where
  pre s :=
    let inner : Region := ⟨(arg s 0).setWidth 64, S.stateBytes⟩
    let outer : Region := ⟨(arg s 1).setWidth 64, S.stateBytes⟩
    let key : Region := ⟨(arg s 2).setWidth 64, (arg s 3).toNat⟩
    let scratch : Region := ⟨(arg s 4).setWidth 64, 8 * W⟩
    let args : Region := ⟨argAddr s 0, 20⟩
    let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
    let stack : Region := ⟨(s.gpr .esp).setWidth 64 - 48, 48⟩
    (arg s 3).toNat ≤ S.H.blockSize ∧ s.rd = [key, args] ∧ s.wr = [inner, outer, scratch] ∧
    inner.Disjoint outer ∧ inner.Disjoint scratch ∧ outer.Disjoint scratch ∧
    key.Disjoint inner ∧ key.Disjoint outer ∧ key.Disjoint scratch ∧
    args.Disjoint inner ∧ args.Disjoint outer ∧ args.Disjoint scratch ∧
    ret.Disjoint inner ∧ ret.Disjoint outer ∧ ret.Disjoint scratch ∧
    stack.Disjoint inner ∧ stack.Disjoint outer ∧ stack.Disjoint key ∧ stack.Disjoint scratch ∧
    (arg s 0).toNat + S.stateBytes ≤ 2 ^ 32 ∧ (arg s 1).toNat + S.stateBytes ≤ 2 ^ 32 ∧
    (arg s 2).toNat + (arg s 3).toNat ≤ 2 ^ 32 ∧ (arg s 4).toNat + 8 * W ≤ 2 ^ 32 ∧
    48 ≤ (s.gpr .esp).toNat ∧ (s.gpr .esp).toNat + 24 ≤ 2 ^ 32
  post s s' :=
    let k0 := blockKey S.H (bytesAt s.mem ((arg s 2).setWidth 64) (arg s 3).toNat)
    S.Repr s'.mem ((arg s 0).setWidth 64) (xorPad k0 ipad) ∧
      S.Repr s'.mem ((arg s 1).setWidth 64) (xorPad k0 opad)
  pub s₁ s₂ := s₁.gpr .esp = s₂.gpr .esp ∧ ∀ i < 5, arg s₁ i = arg s₂ i

/-- `finalize(inner, outer, count, out, scratch)`:
`VG.Spec.Hmac.finalizeContract`, reading its arguments only. -/
def finG : Contract isa where
  pre s :=
    let inner : Region := ⟨(arg s 0).setWidth 64, S.stateBytes⟩
    let outer : Region := ⟨(arg s 1).setWidth 64, S.stateBytes⟩
    let out : Region := ⟨(arg s 4).setWidth 64, S.digestBytes⟩
    let scratch : Region := ⟨(arg s 5).setWidth 64, 8 * W⟩
    let args : Region := ⟨argAddr s 0, 24⟩
    let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
    let stack : Region := ⟨(s.gpr .esp).setWidth 64 - 48, 48⟩
    s.rd = [outer, args] ∧ s.wr = [inner, out, scratch] ∧
    inner.Disjoint outer ∧ inner.Disjoint out ∧ inner.Disjoint scratch ∧
    outer.Disjoint out ∧ outer.Disjoint scratch ∧ out.Disjoint scratch ∧
    args.Disjoint inner ∧ args.Disjoint out ∧ args.Disjoint scratch ∧
    ret.Disjoint inner ∧ ret.Disjoint out ∧ ret.Disjoint scratch ∧
    stack.Disjoint inner ∧ stack.Disjoint outer ∧ stack.Disjoint out ∧ stack.Disjoint scratch ∧
    (arg s 0).toNat + S.stateBytes ≤ 2 ^ 32 ∧ (arg s 1).toNat + S.stateBytes ≤ 2 ^ 32 ∧
    (arg s 4).toNat + S.digestBytes ≤ 2 ^ 32 ∧ (arg s 5).toNat + 8 * W ≤ 2 ^ 32 ∧
    48 ≤ (s.gpr .esp).toNat ∧ (s.gpr .esp).toNat + 28 ≤ 2 ^ 32
  post s s' := ∀ k0 text, k0.length = S.H.blockSize → k0.length + text.length < 2 ^ 64 →
    S.Repr s.mem ((arg s 0).setWidth 64) (xorPad k0 ipad ++ text) →
    countF s = BitVec.ofNat 64 (S.H.blockSize + text.length) →
    S.Repr s.mem ((arg s 1).setWidth 64) (xorPad k0 opad) →
    bytesAt s'.mem ((arg s 4).setWidth 64) S.digestBytes = hmacBlockKey S.H k0 text
  pub s₁ s₂ := s₁.gpr .esp = s₂.gpr .esp ∧ ∀ i < 6, arg s₁ i = arg s₂ i

/-- `iterate(key, u, n, t, scratch)`: `VG.Spec.Pbkdf2.iterateContract`,
reading its arguments only. -/
def iterG : Contract isa where
  pre s :=
    let key : Region := ⟨(arg s 0).setWidth 64, 2 * S.stateBytes⟩
    let u : Region := ⟨(arg s 1).setWidth 64, S.digestBytes⟩
    let t : Region := ⟨(arg s 3).setWidth 64, S.digestBytes⟩
    let scratch : Region := ⟨(arg s 4).setWidth 64, 8 * W⟩
    let args : Region := ⟨argAddr s 0, 20⟩
    let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
    let stack : Region := ⟨(s.gpr .esp).setWidth 64 - 48, 48⟩
    s.rd = [key, u, args] ∧ s.wr = [t, scratch] ∧
    key.Disjoint t ∧ key.Disjoint scratch ∧ u.Disjoint t ∧ u.Disjoint scratch ∧ t.Disjoint scratch ∧
    args.Disjoint t ∧ args.Disjoint scratch ∧ ret.Disjoint t ∧ ret.Disjoint scratch ∧
    stack.Disjoint key ∧ stack.Disjoint u ∧ stack.Disjoint t ∧ stack.Disjoint scratch ∧
    (arg s 0).toNat + 2 * S.stateBytes ≤ 2 ^ 32 ∧ (arg s 1).toNat + S.digestBytes ≤ 2 ^ 32 ∧
    (arg s 3).toNat + S.digestBytes ≤ 2 ^ 32 ∧ (arg s 4).toNat + 8 * W ≤ 2 ^ 32 ∧
    48 ≤ (s.gpr .esp).toNat ∧ (s.gpr .esp).toNat + 24 ≤ 2 ^ 32
  post s s' := ∀ k0, k0.length = S.H.blockSize →
    S.Repr s.mem ((arg s 0).setWidth 64) (xorPad k0 ipad) →
    S.Repr s.mem ((arg s 0).setWidth 64 + BitVec.ofNat 64 S.stateBytes) (xorPad k0 opad) →
    bytesAt s'.mem ((arg s 3).setWidth 64) S.digestBytes =
      Spec.Pbkdf2.iterate (hmacBlockKey S.H k0) (arg s 2).toNat
        (bytesAt s.mem ((arg s 1).setWidth 64) S.digestBytes)
        (bytesAt s.mem ((arg s 3).setWidth 64) S.digestBytes)
  pub s₁ s₂ := s₁.gpr .esp = s₂.gpr .esp ∧ ∀ i < 5, arg s₁ i = arg s₂ i

/-! ## With the arguments writable -/

/-- `initG`, with the arguments writable, as `VG.Spec.Hmac.initContract` has
them. -/
def initW : Contract isa where
  pre s :=
    let inner : Region := ⟨(arg s 0).setWidth 64, S.stateBytes⟩
    let outer : Region := ⟨(arg s 1).setWidth 64, S.stateBytes⟩
    let key : Region := ⟨(arg s 2).setWidth 64, (arg s 3).toNat⟩
    let scratch : Region := ⟨(arg s 4).setWidth 64, 8 * W⟩
    let args : Region := ⟨argAddr s 0, 20⟩
    let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
    let stack : Region := ⟨(s.gpr .esp).setWidth 64 - 48, 48⟩
    (arg s 3).toNat ≤ S.H.blockSize ∧ s.rd = [key] ∧ s.wr = [inner, outer, scratch, args] ∧
    inner.Disjoint outer ∧ inner.Disjoint scratch ∧ outer.Disjoint scratch ∧
    key.Disjoint inner ∧ key.Disjoint outer ∧ key.Disjoint scratch ∧
    args.Disjoint inner ∧ args.Disjoint outer ∧ args.Disjoint scratch ∧
    ret.Disjoint inner ∧ ret.Disjoint outer ∧ ret.Disjoint scratch ∧
    stack.Disjoint inner ∧ stack.Disjoint outer ∧ stack.Disjoint key ∧ stack.Disjoint scratch ∧
    (arg s 0).toNat + S.stateBytes ≤ 2 ^ 32 ∧ (arg s 1).toNat + S.stateBytes ≤ 2 ^ 32 ∧
    (arg s 2).toNat + (arg s 3).toNat ≤ 2 ^ 32 ∧ (arg s 4).toNat + 8 * W ≤ 2 ^ 32 ∧
    48 ≤ (s.gpr .esp).toNat ∧ (s.gpr .esp).toNat + 24 ≤ 2 ^ 32
  post := (initG S W).post
  pub := (initG S W).pub

/-- `finG`, with the arguments writable, as `VG.Spec.Hmac.finalizeContract`
has them. -/
def finW : Contract isa where
  pre s :=
    let inner : Region := ⟨(arg s 0).setWidth 64, S.stateBytes⟩
    let outer : Region := ⟨(arg s 1).setWidth 64, S.stateBytes⟩
    let out : Region := ⟨(arg s 4).setWidth 64, S.digestBytes⟩
    let scratch : Region := ⟨(arg s 5).setWidth 64, 8 * W⟩
    let args : Region := ⟨argAddr s 0, 24⟩
    let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
    let stack : Region := ⟨(s.gpr .esp).setWidth 64 - 48, 48⟩
    s.rd = [outer] ∧ s.wr = [inner, out, scratch, args] ∧
    inner.Disjoint outer ∧ inner.Disjoint out ∧ inner.Disjoint scratch ∧
    outer.Disjoint out ∧ outer.Disjoint scratch ∧ out.Disjoint scratch ∧
    args.Disjoint inner ∧ args.Disjoint out ∧ args.Disjoint scratch ∧
    ret.Disjoint inner ∧ ret.Disjoint out ∧ ret.Disjoint scratch ∧
    stack.Disjoint inner ∧ stack.Disjoint outer ∧ stack.Disjoint out ∧ stack.Disjoint scratch ∧
    (arg s 0).toNat + S.stateBytes ≤ 2 ^ 32 ∧ (arg s 1).toNat + S.stateBytes ≤ 2 ^ 32 ∧
    (arg s 4).toNat + S.digestBytes ≤ 2 ^ 32 ∧ (arg s 5).toNat + 8 * W ≤ 2 ^ 32 ∧
    48 ≤ (s.gpr .esp).toNat ∧ (s.gpr .esp).toNat + 28 ≤ 2 ^ 32
  post := (finG S W).post
  pub := (finG S W).pub

/-- `iterG`, with the arguments writable, as `VG.Spec.Pbkdf2.iterateContract`
has them. -/
def iterW : Contract isa where
  pre s :=
    let key : Region := ⟨(arg s 0).setWidth 64, 2 * S.stateBytes⟩
    let u : Region := ⟨(arg s 1).setWidth 64, S.digestBytes⟩
    let t : Region := ⟨(arg s 3).setWidth 64, S.digestBytes⟩
    let scratch : Region := ⟨(arg s 4).setWidth 64, 8 * W⟩
    let args : Region := ⟨argAddr s 0, 20⟩
    let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
    let stack : Region := ⟨(s.gpr .esp).setWidth 64 - 48, 48⟩
    s.rd = [key, u] ∧ s.wr = [t, scratch, args] ∧
    key.Disjoint t ∧ key.Disjoint scratch ∧ u.Disjoint t ∧ u.Disjoint scratch ∧ t.Disjoint scratch ∧
    args.Disjoint t ∧ args.Disjoint scratch ∧ ret.Disjoint t ∧ ret.Disjoint scratch ∧
    stack.Disjoint key ∧ stack.Disjoint u ∧ stack.Disjoint t ∧ stack.Disjoint scratch ∧
    (arg s 0).toNat + 2 * S.stateBytes ≤ 2 ^ 32 ∧ (arg s 1).toNat + S.digestBytes ≤ 2 ^ 32 ∧
    (arg s 3).toNat + S.digestBytes ≤ 2 ^ 32 ∧ (arg s 4).toNat + 8 * W ≤ 2 ^ 32 ∧
    48 ≤ (s.gpr .esp).toNat ∧ (s.gpr .esp).toNat + 24 ≤ 2 ^ 32
  post := (iterG S W).post
  pub := (iterG S W).pub

end VG.Proof.Hmac.Generic.X86
