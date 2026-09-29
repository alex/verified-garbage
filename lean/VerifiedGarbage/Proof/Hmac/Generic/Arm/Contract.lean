import VerifiedGarbage.Spec.Pbkdf2.Generic
import VerifiedGarbage.TCB.Arm.Target

/-!
# HMAC and PBKDF2-HMAC over any streaming hash function: the 32-bit ARM contracts

**Untrusted**: the contracts the proofs are written against, as on x86-64
and AArch64 (`Proof/Hmac/Generic/AArch64/Contract.lean`).

* `initK`, `updK` and `finK` are the 32-bit ARM contracts of a hash
  function's streaming `init`, `update` and `finalize` (`Proof.Sha1.initArm`
  and the others), with the sizes and the representation of the streaming
  state as parameters. Under AAPCS `count` is in `r2:r3`, and `update`'s
  `data`, `len` and `scratch` and `finalize`'s `out` and `scratch` are
  stack arguments.
* `initG`, `finG` and `iterG` are those of our functions, which push up to
  16 bytes of stack (the stack arguments of the functions they call), which
  no buffer overlaps; the artifacts are emitted with the shared contracts of
  `Spec/Hmac/Generic.lean` and `Spec/Pbkdf2/Generic.lean`, which imply them
  (`Contract.Implies`).
-/

namespace VG.Proof.Hmac.Generic.Arm

open VG.Arm
open Spec.Hmac (StreamingHash xorPad ipad opad blockKey hmacBlockKey)
open Spec.Sha256 (bytesAt)

/-- The 16 bytes below the stack pointer. -/
abbrev below (s : State) : Region := ⟨State.addr s.sp - 16, 16⟩

/-- The 64-bit `count` argument, in `r2:r3` (AAPCS: the low word in `r2`). -/
def count (s : State) : BitVec 64 := s.gpr .r3 ++ s.gpr .r2

/-! ## The functions we call -/

/-- `init(state)`: makes the `S`-byte streaming state at `state` represent the
empty message. -/
def initK (S : Nat) (R : Mem → Addr → List Byte → Prop) : Contract isa where
  pre s :=
    s.rd = [] ∧ s.wr = [⟨State.addr (s.gpr .r0), S⟩] ∧ (s.gpr .r0).toNat + S ≤ 2 ^ 32
  post s s' := R s'.mem (State.addr (s.gpr .r0)) []
  pub s₁ s₂ := s₁.gpr .r0 = s₂.gpr .r0

/-- `update(state, count, data, len, scratch)`, with `Wb` bytes of scratch
space. -/
def updK (S Wb : Nat) (R : Mem → Addr → List Byte → Prop) : Contract isa where
  pre s :=
    let state : Region := ⟨State.addr (s.gpr .r0), S⟩
    let data : Region := ⟨State.addr (stackArg s 0), (stackArg s 1).toNat⟩
    let scratch : Region := ⟨State.addr (stackArg s 2), Wb⟩
    let args : Region := ⟨stackArgAddr s 0, 12⟩
    s.rd = [data, args] ∧ s.wr = [state, scratch] ∧
    state.Disjoint scratch ∧ data.Disjoint state ∧ data.Disjoint scratch ∧
    args.Disjoint state ∧ args.Disjoint scratch ∧
    (s.gpr .r0).toNat + S ≤ 2 ^ 32 ∧ (stackArg s 0).toNat + (stackArg s 1).toNat ≤ 2 ^ 32 ∧
    (stackArg s 2).toNat + Wb ≤ 2 ^ 32 ∧ s.sp.toNat + 12 ≤ 2 ^ 32
  post s s' := ∀ m, R s.mem (State.addr (s.gpr .r0)) m → count s = BitVec.ofNat 64 m.length →
    R s'.mem (State.addr (s.gpr .r0)) (m ++ bytesAt s.mem (State.addr (stackArg s 0)) (stackArg s 1).toNat)
  pub s₁ s₂ :=
    s₁.sp = s₂.sp ∧ s₁.gpr .r0 = s₂.gpr .r0 ∧ s₁.gpr .r2 = s₂.gpr .r2 ∧ s₁.gpr .r3 = s₂.gpr .r3 ∧
    stackArg s₁ 0 = stackArg s₂ 0 ∧ stackArg s₁ 1 = stackArg s₂ 1 ∧ stackArg s₁ 2 = stackArg s₂ 2

/-- `finalize(state, count, out, scratch)`, writing `F` bytes whose first
`D` are the digest `hash m`, for a message of fewer than 2⁶⁴ bytes. -/
def finK (S Wb F D : Nat) (R : Mem → Addr → List Byte → Prop) (hash : List Byte → List Byte) :
    Contract isa where
  pre s :=
    let state : Region := ⟨State.addr (s.gpr .r0), S⟩
    let out : Region := ⟨State.addr (stackArg s 0), F⟩
    let scratch : Region := ⟨State.addr (stackArg s 1), Wb⟩
    let args : Region := ⟨stackArgAddr s 0, 8⟩
    s.rd = [args] ∧ s.wr = [state, out, scratch] ∧
    state.Disjoint out ∧ state.Disjoint scratch ∧ out.Disjoint scratch ∧
    args.Disjoint state ∧ args.Disjoint out ∧ args.Disjoint scratch ∧
    (s.gpr .r0).toNat + S ≤ 2 ^ 32 ∧ (stackArg s 0).toNat + F ≤ 2 ^ 32 ∧
    (stackArg s 1).toNat + Wb ≤ 2 ^ 32 ∧ s.sp.toNat + 8 ≤ 2 ^ 32
  post s s' := ∀ m, R s.mem (State.addr (s.gpr .r0)) m → m.length < 2 ^ 64 →
    count s = BitVec.ofNat 64 m.length → (bytesAt s'.mem (State.addr (stackArg s 0)) F).take D = hash m
  pub s₁ s₂ :=
    s₁.sp = s₂.sp ∧ s₁.gpr .r0 = s₂.gpr .r0 ∧ s₁.gpr .r2 = s₂.gpr .r2 ∧ s₁.gpr .r3 = s₂.gpr .r3 ∧
    stackArg s₁ 0 = stackArg s₂ 0 ∧ stackArg s₁ 1 = stackArg s₂ 1

/-! ## Our functions

`S` is a streaming hash function and `W` the number of 64-bit words of
scratch space. -/

variable (S : StreamingHash) (W : Nat)

/-- `init(inner, outer, key, key_len, scratch)`: `VG.Spec.Hmac.initContract`. -/
def initG : Contract isa where
  pre s :=
    let inner : Region := ⟨State.addr (s.gpr .r0), S.stateBytes⟩
    let outer : Region := ⟨State.addr (s.gpr .r1), S.stateBytes⟩
    let key : Region := ⟨State.addr (s.gpr .r2), (s.gpr .r3).toNat⟩
    let scratch : Region := ⟨State.addr (stackArg s 0), 8 * W⟩
    let args : Region := ⟨stackArgAddr s 0, 4⟩
    (s.gpr .r3).toNat ≤ S.H.blockSize ∧ s.rd = [key, args] ∧ s.wr = [inner, outer, scratch] ∧
    inner.Disjoint outer ∧ inner.Disjoint scratch ∧ outer.Disjoint scratch ∧
    key.Disjoint inner ∧ key.Disjoint outer ∧ key.Disjoint scratch ∧
    args.Disjoint inner ∧ args.Disjoint outer ∧ args.Disjoint scratch ∧
    (below s).Disjoint inner ∧ (below s).Disjoint outer ∧ (below s).Disjoint key ∧
    (below s).Disjoint scratch ∧
    (s.gpr .r0).toNat + S.stateBytes ≤ 2 ^ 32 ∧ (s.gpr .r1).toNat + S.stateBytes ≤ 2 ^ 32 ∧
    (s.gpr .r2).toNat + (s.gpr .r3).toNat ≤ 2 ^ 32 ∧ (stackArg s 0).toNat + 8 * W ≤ 2 ^ 32 ∧
    16 ≤ s.sp.toNat ∧ s.sp.toNat + 4 ≤ 2 ^ 32
  post s s' :=
    let k0 := blockKey S.H (bytesAt s.mem (State.addr (s.gpr .r2)) (s.gpr .r3).toNat)
    S.Repr s'.mem (State.addr (s.gpr .r0)) (xorPad k0 ipad) ∧
      S.Repr s'.mem (State.addr (s.gpr .r1)) (xorPad k0 opad)
  pub s₁ s₂ :=
    s₁.sp = s₂.sp ∧ s₁.gpr .r0 = s₂.gpr .r0 ∧ s₁.gpr .r1 = s₂.gpr .r1 ∧
    s₁.gpr .r2 = s₂.gpr .r2 ∧ s₁.gpr .r3 = s₂.gpr .r3 ∧ stackArg s₁ 0 = stackArg s₂ 0

/-- `finalize(inner, outer, count, out, scratch)`: `VG.Spec.Hmac.finalizeContract`. -/
def finG : Contract isa where
  pre s :=
    let inner : Region := ⟨State.addr (s.gpr .r0), S.stateBytes⟩
    let outer : Region := ⟨State.addr (s.gpr .r1), S.stateBytes⟩
    let out : Region := ⟨State.addr (stackArg s 0), S.digestBytes⟩
    let scratch : Region := ⟨State.addr (stackArg s 1), 8 * W⟩
    let args : Region := ⟨stackArgAddr s 0, 8⟩
    s.rd = [outer, args] ∧ s.wr = [inner, out, scratch] ∧
    inner.Disjoint outer ∧ inner.Disjoint out ∧ inner.Disjoint scratch ∧
    outer.Disjoint out ∧ outer.Disjoint scratch ∧ out.Disjoint scratch ∧
    args.Disjoint inner ∧ args.Disjoint out ∧ args.Disjoint scratch ∧
    (below s).Disjoint inner ∧ (below s).Disjoint outer ∧ (below s).Disjoint out ∧
    (below s).Disjoint scratch ∧
    (s.gpr .r0).toNat + S.stateBytes ≤ 2 ^ 32 ∧ (s.gpr .r1).toNat + S.stateBytes ≤ 2 ^ 32 ∧
    (stackArg s 0).toNat + S.digestBytes ≤ 2 ^ 32 ∧ (stackArg s 1).toNat + 8 * W ≤ 2 ^ 32 ∧
    16 ≤ s.sp.toNat ∧ s.sp.toNat + 8 ≤ 2 ^ 32
  post s s' := ∀ k0 text, k0.length = S.H.blockSize → k0.length + text.length < 2 ^ 64 →
    S.Repr s.mem (State.addr (s.gpr .r0)) (xorPad k0 ipad ++ text) →
    count s = BitVec.ofNat 64 (S.H.blockSize + text.length) →
    S.Repr s.mem (State.addr (s.gpr .r1)) (xorPad k0 opad) →
    bytesAt s'.mem (State.addr (stackArg s 0)) S.digestBytes = hmacBlockKey S.H k0 text
  pub s₁ s₂ :=
    s₁.sp = s₂.sp ∧ s₁.gpr .r0 = s₂.gpr .r0 ∧ s₁.gpr .r1 = s₂.gpr .r1 ∧
    s₁.gpr .r2 = s₂.gpr .r2 ∧ s₁.gpr .r3 = s₂.gpr .r3 ∧
    stackArg s₁ 0 = stackArg s₂ 0 ∧ stackArg s₁ 1 = stackArg s₂ 1

/-- `iterate(key, u, n, t, scratch)`: `VG.Spec.Pbkdf2.iterateContract`. -/
def iterG : Contract isa where
  pre s :=
    let key : Region := ⟨State.addr (s.gpr .r0), 2 * S.stateBytes⟩
    let u : Region := ⟨State.addr (s.gpr .r1), S.digestBytes⟩
    let t : Region := ⟨State.addr (s.gpr .r3), S.digestBytes⟩
    let scratch : Region := ⟨State.addr (stackArg s 0), 8 * W⟩
    let args : Region := ⟨stackArgAddr s 0, 4⟩
    s.rd = [key, u, args] ∧ s.wr = [t, scratch] ∧
    key.Disjoint t ∧ key.Disjoint scratch ∧ u.Disjoint t ∧ u.Disjoint scratch ∧ t.Disjoint scratch ∧
    args.Disjoint t ∧ args.Disjoint scratch ∧
    (below s).Disjoint key ∧ (below s).Disjoint u ∧ (below s).Disjoint t ∧ (below s).Disjoint scratch ∧
    (s.gpr .r0).toNat + 2 * S.stateBytes ≤ 2 ^ 32 ∧ (s.gpr .r1).toNat + S.digestBytes ≤ 2 ^ 32 ∧
    (s.gpr .r3).toNat + S.digestBytes ≤ 2 ^ 32 ∧ (stackArg s 0).toNat + 8 * W ≤ 2 ^ 32 ∧
    16 ≤ s.sp.toNat ∧ s.sp.toNat + 4 ≤ 2 ^ 32
  post s s' := ∀ k0, k0.length = S.H.blockSize →
    S.Repr s.mem (State.addr (s.gpr .r0)) (xorPad k0 ipad) →
    S.Repr s.mem (State.addr (s.gpr .r0) + BitVec.ofNat 64 S.stateBytes) (xorPad k0 opad) →
    bytesAt s'.mem (State.addr (s.gpr .r3)) S.digestBytes =
      Spec.Pbkdf2.iterate (hmacBlockKey S.H k0) (s.gpr .r2).toNat
        (bytesAt s.mem (State.addr (s.gpr .r1)) S.digestBytes)
        (bytesAt s.mem (State.addr (s.gpr .r3)) S.digestBytes)
  pub s₁ s₂ :=
    s₁.sp = s₂.sp ∧ s₁.gpr .r0 = s₂.gpr .r0 ∧ s₁.gpr .r1 = s₂.gpr .r1 ∧
    s₁.gpr .r2 = s₂.gpr .r2 ∧ s₁.gpr .r3 = s₂.gpr .r3 ∧ stackArg s₁ 0 = stackArg s₂ 0

end VG.Proof.Hmac.Generic.Arm
