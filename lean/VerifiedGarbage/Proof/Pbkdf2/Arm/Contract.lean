import VerifiedGarbage.Spec.Pbkdf2
import VerifiedGarbage.Proof.Sha256.Arm.Contract

/-!
# PBKDF2-HMAC-SHA-256's iteration: the 32-bit ARM contract

**Untrusted**: the contract the proof is written against; the artifact is
emitted with the shared contract of `Spec/Pbkdf2/Contract.lean`, which
implies this one (`Contract.Implies`).
-/

namespace VG.Proof.Pbkdf2

open Spec.Hmac (xorPad ipad opad hmacBlockKey sha256)
open Spec.Sha256 (Repr bytesAt)

open Arm in
/-- 32-bit ARM contract for
`vg_pbkdf2_hmac_sha256_iterate(key: *const [u8; 192], u: *const [u8; 32], n: u32, t: *mut [u8; 32], scratch: *mut [u64; 48])`:
if, for a 64-byte key `K₀`, the streaming state at `key` represents
`K₀ ⊕ ipad` and the one at `key + 96` represents `K₀ ⊕ opad`, runs `n` steps
`U ← HMAC-SHA-256 (K₀, U)`, `T ← T ⊕ U` from the `U` at `u` and the `T` at
`t`, leaving the final `T` at `t`.

Under AAPCS, `key`, `u`, `n` and `t` are in `r0`–`r3`, and `scratch` is the
stack argument 0. The code may read that argument (4 bytes at `sp`), `key`
(192 bytes) and `u` (32 bytes), and read and write `t` (32 bytes) and
`scratch` (384 bytes, whose contents on exit are unspecified). The written
regions may not overlap each other, the read ones or the argument; and
nothing may wrap around the end of the (32-bit) address space. `sp`, the
pointers and `n` are public; the key, `U` and `T` are secret. -/
def iterateSha256Arm : Contract isa where
  pre s :=
    let key : Region := ⟨State.addr (s.gpr .r0), 192⟩
    let u : Region := ⟨State.addr (s.gpr .r1), 32⟩
    let t : Region := ⟨State.addr (s.gpr .r3), 32⟩
    let scratch : Region := ⟨State.addr (stackArg s 0), 384⟩
    let args : Region := ⟨stackArgAddr s 0, 4⟩
    s.rd = [key, u, args] ∧ s.wr = [t, scratch] ∧
    key.Disjoint t ∧ key.Disjoint scratch ∧ u.Disjoint t ∧ u.Disjoint scratch ∧ t.Disjoint scratch ∧
    args.Disjoint t ∧ args.Disjoint scratch ∧
    (s.gpr .r0).toNat + 192 ≤ 2 ^ 32 ∧ (s.gpr .r1).toNat + 32 ≤ 2 ^ 32 ∧
    (s.gpr .r3).toNat + 32 ≤ 2 ^ 32 ∧ (stackArg s 0).toNat + 384 ≤ 2 ^ 32 ∧
    s.sp.toNat + 4 ≤ 2 ^ 32
  post s s' := ∀ k0, k0.length = 64 →
    Repr s.mem (State.addr (s.gpr .r0)) (xorPad k0 ipad) →
    Repr s.mem (State.addr (s.gpr .r0) + 96) (xorPad k0 opad) →
    bytesAt s'.mem (State.addr (s.gpr .r3)) 32 =
      Spec.Pbkdf2.iterate (hmacBlockKey sha256 k0) (s.gpr .r2).toNat
        (bytesAt s.mem (State.addr (s.gpr .r1)) 32) (bytesAt s.mem (State.addr (s.gpr .r3)) 32)
  pub s₁ s₂ :=
    s₁.sp = s₂.sp ∧ s₁.gpr .r0 = s₂.gpr .r0 ∧ s₁.gpr .r1 = s₂.gpr .r1 ∧
    s₁.gpr .r2 = s₂.gpr .r2 ∧ s₁.gpr .r3 = s₂.gpr .r3 ∧ stackArg s₁ 0 = stackArg s₂ 0

end VG.Proof.Pbkdf2
