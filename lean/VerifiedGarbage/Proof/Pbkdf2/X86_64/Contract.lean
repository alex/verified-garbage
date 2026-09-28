import VerifiedGarbage.Spec.Pbkdf2
import VerifiedGarbage.Proof.Sha256.X86_64.Contract

/-!
# PBKDF2-HMAC-SHA-256's iteration: the x86-64 contract

**Untrusted**: the contract the proof is written against; the artifact is
emitted with the shared contract of `Spec/Pbkdf2/Contract.lean`, which
implies this one (`Contract.Implies`).
-/

namespace VG.Proof.Pbkdf2

open Spec.Hmac (xorPad ipad opad hmacBlockKey sha256)
open Spec.Sha256 (Repr bytesAt)

open X86_64 in
/-- x86-64 contract for
`vg_pbkdf2_hmac_sha256_iterate(key: *const [u8; 192], u: *const [u8; 32], n: u32, t: *mut [u8; 32], scratch: *mut [u64; 48])`:
if, for a 64-byte key `K₀`, the streaming state at `key` represents
`K₀ ⊕ ipad` and the one at `key + 96` represents `K₀ ⊕ opad`, runs `n` steps
`U ← HMAC-SHA-256 (K₀, U)`, `T ← T ⊕ U` from the `U` at `u` and the `T` at
`t`, leaving the final `T` at `t`.

The code may read `key` (192 bytes) and `u` (32 bytes), and read and write
`t` (32 bytes) and `scratch` (384 bytes, whose contents on exit are
unspecified). The written regions may not overlap each other or the read
ones, nor the return address and the 8 bytes below it (where its calls of
`vg_sha256_compress` store their return address). The pointers and `n` are
public (`n` only in the low 32 bits of `rdx`); the key, `U` and `T` are secret. -/
def iterateSha256X86_64 : Contract isa where
  pre s :=
    let key : Region := ⟨s.gpr .rdi, 192⟩
    let u : Region := ⟨s.gpr .rsi, 32⟩
    let t : Region := ⟨s.gpr .rcx, 32⟩
    let scratch : Region := ⟨s.gpr .r8, 384⟩
    let ret : Region := ⟨s.gpr .rsp, 8⟩
    let stack : Region := ⟨s.gpr .rsp - 8, 8⟩
    s.rd = [key, u] ∧ s.wr = [t, scratch] ∧
    key.Disjoint t ∧ key.Disjoint scratch ∧ u.Disjoint t ∧ u.Disjoint scratch ∧ t.Disjoint scratch ∧
    ret.Disjoint key ∧ ret.Disjoint u ∧ ret.Disjoint t ∧ ret.Disjoint scratch ∧
    stack.Disjoint key ∧ stack.Disjoint u ∧ stack.Disjoint t ∧ stack.Disjoint scratch
  post s s' := ∀ k0, k0.length = 64 →
    Repr s.mem (s.gpr .rdi) (xorPad k0 ipad) → Repr s.mem (s.gpr .rdi + 96) (xorPad k0 opad) →
    bytesAt s'.mem (s.gpr .rcx) 32 =
      Spec.Pbkdf2.iterate (hmacBlockKey sha256 k0) ((s.gpr .rdx).setWidth 32).toNat
        (bytesAt s.mem (s.gpr .rsi) 32) (bytesAt s.mem (s.gpr .rcx) 32)
  pub s₁ s₂ :=
    s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ (s₁.gpr .rdx).setWidth 32 = (s₂.gpr .rdx).setWidth 32 ∧
    s₁.gpr .rcx = s₂.gpr .rcx ∧ s₁.gpr .r8 = s₂.gpr .r8 ∧ s₁.gpr .rsp = s₂.gpr .rsp

end VG.Proof.Pbkdf2
