import VerifiedGarbage.Spec.Hmac
import VerifiedGarbage.Spec.Sha256.Arm

/-!
# HMAC-SHA-256: the 32-bit ARM contracts

**Trusted** (as every file in `Spec/`). The same functions as on x86-64
(`VerifiedGarbage/Spec/Hmac/X86_64.lean`): an HMAC-SHA-256 computation is two
SHA-256 streaming states (`VG.Spec.Sha256.Repr`), the inner one, which
absorbs `(K₀ ⊕ ipad) ‖ text`, and the outer one, which holds `K₀ ⊕ opad`.
`vg_hmac_sha256_init` sets them up from the key, the text is absorbed into
the inner state with `vg_sha256_update` (`VG.Spec.Sha256.updateArm`), and
`vg_hmac_sha256_finalize` computes the MAC.

Under AAPCS the first four words of arguments are in `r0`–`r3` (a 64-bit
argument in an even-odd pair, low word first) and the rest on the stack at
`sp`. `vg_hmac_sha256_init` has the x86-64 signature. `vg_hmac_sha256_finalize`
writes the MAC through an `out` pointer instead of leaving it in `scratch`:
its `count` fills `r2:r3`, so `out` and `scratch` are its two stack
arguments, laid out as the stack arguments of `vg_sha256_finalize`
(`VG.Spec.Sha256.finalizeArm`) are.
-/

namespace VG.Spec.Hmac

open Sha256 (Repr bytesAt)

open Arm in
/-- 32-bit ARM contract for
`vg_hmac_sha256_init(inner: *mut [u8; 96], outer: *mut [u8; 96], key: *const u8, key_len: usize, scratch: *mut [u64; 20])`,
for a key of at most 64 bytes (the SHA-256 block size): makes the streaming
state at `inner` represent `K₀ ⊕ ipad` and the one at `outer` represent
`K₀ ⊕ opad`, for the key `K₀` made of the `key_len` bytes at `key`.

Under AAPCS, `inner`, `outer`, `key` and `key_len` are in `r0`–`r3`, and
`scratch` is the stack argument 0. The code may read that argument (4 bytes
at `sp`) and `key` (`key_len` bytes), and read and write `inner` and `outer`
(96 bytes each) and `scratch` (160 bytes, whose contents on exit are
unspecified). The writable buffers may not overlap each other, the key or
the argument; and nothing may wrap around the end of the (32-bit) address
space. `sp`, the pointers and `key_len` are public; the key is secret. -/
def initSha256Arm : Contract Arm.isa where
  pre s :=
    let inner : Region := ⟨State.addr (s.gpr .r0), 96⟩
    let outer : Region := ⟨State.addr (s.gpr .r1), 96⟩
    let key : Region := ⟨State.addr (s.gpr .r2), (s.gpr .r3).toNat⟩
    let scratch : Region := ⟨State.addr (stackArg s 0), 160⟩
    let args : Region := ⟨stackArgAddr s 0, 4⟩
    (s.gpr .r3).toNat ≤ 64 ∧ s.rd = [key, args] ∧ s.wr = [inner, outer, scratch] ∧
    inner.Disjoint outer ∧ inner.Disjoint scratch ∧ outer.Disjoint scratch ∧
    key.Disjoint inner ∧ key.Disjoint outer ∧ key.Disjoint scratch ∧
    args.Disjoint inner ∧ args.Disjoint outer ∧ args.Disjoint scratch ∧
    (s.gpr .r0).toNat + 96 ≤ 2 ^ 32 ∧ (s.gpr .r1).toNat + 96 ≤ 2 ^ 32 ∧
    (s.gpr .r2).toNat + (s.gpr .r3).toNat ≤ 2 ^ 32 ∧ (stackArg s 0).toNat + 160 ≤ 2 ^ 32 ∧
    s.sp.toNat + 4 ≤ 2 ^ 32
  post s s' :=
    let k0 := blockKey sha256 (bytesAt s.mem (State.addr (s.gpr .r2)) (s.gpr .r3).toNat)
    Repr s'.mem (State.addr (s.gpr .r0)) (xorPad k0 ipad) ∧
      Repr s'.mem (State.addr (s.gpr .r1)) (xorPad k0 opad)
  pub s₁ s₂ :=
    s₁.sp = s₂.sp ∧ s₁.gpr .r0 = s₂.gpr .r0 ∧ s₁.gpr .r1 = s₂.gpr .r1 ∧
    s₁.gpr .r2 = s₂.gpr .r2 ∧ s₁.gpr .r3 = s₂.gpr .r3 ∧ stackArg s₁ 0 = stackArg s₂ 0

open Arm in
/-- 32-bit ARM contract for
`vg_hmac_sha256_finalize(inner: *mut [u8; 96], outer: *const [u8; 96], count: u64, out: *mut [u8; 32], scratch: *mut [u64; 30])`:
if, for a 64-byte key `K₀` and a text, the streaming state at `inner`
represents `(K₀ ⊕ ipad) ‖ text`, of `count` bytes (modulo 2⁶⁴), and the one at
`outer` represents `K₀ ⊕ opad`, writes the HMAC-SHA-256 of the text under
`K₀` to `out`.

Under AAPCS, `inner` and `outer` are in `r0` and `r1`, `count` in `r2:r3`,
and `out` and `scratch` are the stack arguments 0 and 1. The code may read
those arguments (8 bytes at `sp`) and `outer` (96 bytes), and read and write
`inner` (96 bytes, whose contents on exit are unspecified), `out` (32 bytes)
and `scratch` (240 bytes, whose contents on exit are unspecified). The
writable buffers may not overlap each other, `outer` or the arguments; and
nothing may wrap around the end of the (32-bit) address space. `sp`, the
pointers and `count` are public; the states are secret. -/
def finalizeSha256Arm : Contract Arm.isa where
  pre s :=
    let inner : Region := ⟨State.addr (s.gpr .r0), 96⟩
    let outer : Region := ⟨State.addr (s.gpr .r1), 96⟩
    let out : Region := ⟨State.addr (stackArg s 0), 32⟩
    let scratch : Region := ⟨State.addr (stackArg s 1), 240⟩
    let args : Region := ⟨stackArgAddr s 0, 8⟩
    s.rd = [outer, args] ∧ s.wr = [inner, out, scratch] ∧
    inner.Disjoint out ∧ inner.Disjoint scratch ∧ out.Disjoint scratch ∧
    outer.Disjoint inner ∧ outer.Disjoint out ∧ outer.Disjoint scratch ∧
    args.Disjoint inner ∧ args.Disjoint out ∧ args.Disjoint scratch ∧
    (s.gpr .r0).toNat + 96 ≤ 2 ^ 32 ∧ (s.gpr .r1).toNat + 96 ≤ 2 ^ 32 ∧
    (stackArg s 0).toNat + 32 ≤ 2 ^ 32 ∧ (stackArg s 1).toNat + 240 ≤ 2 ^ 32 ∧
    s.sp.toNat + 8 ≤ 2 ^ 32
  post s s' := ∀ k0 text, k0.length = 64 →
    Repr s.mem (State.addr (s.gpr .r0)) (xorPad k0 ipad ++ text) →
    Sha256.countArm s = BitVec.ofNat 64 (64 + text.length) →
    Repr s.mem (State.addr (s.gpr .r1)) (xorPad k0 opad) →
    bytesAt s'.mem (State.addr (stackArg s 0)) 32 = hmacBlockKey sha256 k0 text
  pub s₁ s₂ :=
    s₁.sp = s₂.sp ∧ s₁.gpr .r0 = s₂.gpr .r0 ∧ s₁.gpr .r1 = s₂.gpr .r1 ∧
    s₁.gpr .r2 = s₂.gpr .r2 ∧ s₁.gpr .r3 = s₂.gpr .r3 ∧
    stackArg s₁ 0 = stackArg s₂ 0 ∧ stackArg s₁ 1 = stackArg s₂ 1

end VG.Spec.Hmac
