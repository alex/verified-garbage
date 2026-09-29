import VerifiedGarbage.Spec.Pbkdf2
import VerifiedGarbage.Proof.Sha256.AArch64.Contract

/-!
# PBKDF2-HMAC-SHA-256: the AArch64 contracts

**Untrusted**: the contracts the proofs are written against; the artifacts are
emitted with the shared contracts of `Spec/Pbkdf2/Contract.lean`, which
imply these (`Contract.Implies`).
-/

namespace VG.Proof.Pbkdf2

open Spec.Hmac (xorPad ipad opad hmacBlockKey sha256)
open Spec.Sha256 (Repr bytesAt)

open AArch64 in
/-- AArch64 contract for
`vg_pbkdf2_hmac_sha256_iterate(key: *const [u8; 192], u: *const [u8; 32], n: u32, t: *mut [u8; 32], scratch: *mut [u64; 48])`:
if, for a 64-byte key `K₀`, the streaming state at `key` represents
`K₀ ⊕ ipad` and the one at `key + 96` represents `K₀ ⊕ opad`, runs `n` steps
`U ← HMAC-SHA-256 (K₀, U)`, `T ← T ⊕ U` from the `U` at `u` and the `T` at
`t`, leaving the final `T` at `t`.

The code may read `key` (192 bytes) and `u` (32 bytes), and read and write
`t` (32 bytes) and `scratch` (384 bytes, whose contents on exit are
unspecified). The written regions may not overlap each other or the read
ones. The return address is in `x30` and saved in `scratch`, so no stack is
used. The pointers and `n` are public (`n` only in the low 32 bits of `x2`);
the key, `U` and `T` are secret. -/
def iterateSha256AArch64 : Contract isa where
  pre s :=
    let key : Region := ⟨s.gpr .x0, 192⟩
    let u : Region := ⟨s.gpr .x1, 32⟩
    let t : Region := ⟨s.gpr .x3, 32⟩
    let scratch : Region := ⟨s.gpr .x4, 384⟩
    s.rd = [key, u] ∧ s.wr = [t, scratch] ∧
    key.Disjoint t ∧ key.Disjoint scratch ∧ u.Disjoint t ∧ u.Disjoint scratch ∧ t.Disjoint scratch
  post s s' := ∀ k0, k0.length = 64 →
    Repr s.mem (s.gpr .x0) (xorPad k0 ipad) → Repr s.mem (s.gpr .x0 + 96) (xorPad k0 opad) →
    bytesAt s'.mem (s.gpr .x3) 32 =
      Spec.Pbkdf2.iterate (hmacBlockKey sha256 k0) ((s.gpr .x2).setWidth 32).toNat
        (bytesAt s.mem (s.gpr .x1) 32) (bytesAt s.mem (s.gpr .x3) 32)
  pub s₁ s₂ :=
    s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ (s₁.gpr .x2).setWidth 32 = (s₂.gpr .x2).setWidth 32 ∧
    s₁.gpr .x3 = s₂.gpr .x3 ∧ s₁.gpr .x4 = s₂.gpr .x4 ∧ s₁.sp = s₂.sp

open AArch64 in
/-- AArch64 contract for
`vg_pbkdf2_hmac_sha256(password: *const u8, password_len: usize, salt: *const u8, salt_len: usize, c: u32, out: *mut u8, out_len: usize, scratch: *mut [u64; 256])`:
if `c > 0` and `out_len ≤ (2³² − 1) · 32`, writes PBKDF2-HMAC-SHA-256 of the
password and the salt with `c` iterations to the `out_len` bytes at `out`.

The code may read the password and the salt, and read and write `out` and
`scratch` (2048 bytes, whose contents on exit are unspecified). The written
regions may not overlap each other or the read ones, and none may overlap
the 48 bytes below the stack pointer (the frames saving `x30` here and in
the functions it calls), which do not wrap around, or wrap around the end of
the address space. The pointers, the lengths and `c` (only in the low 32
bits of `x4`) are public. -/
def pbkdf2Sha256AArch64 : Contract isa where
  pre s :=
    let pw : Region := ⟨s.gpr .x0, (s.gpr .x1).toNat⟩
    let salt : Region := ⟨s.gpr .x2, (s.gpr .x3).toNat⟩
    let out : Region := ⟨s.gpr .x5, (s.gpr .x6).toNat⟩
    let scratch : Region := ⟨s.gpr .x7, 2048⟩
    let stack : Region := ⟨s.sp - 48, 48⟩
    s.rd = [pw, salt] ∧ s.wr = [out, scratch] ∧
    pw.Disjoint out ∧ pw.Disjoint scratch ∧ salt.Disjoint out ∧ salt.Disjoint scratch ∧
    out.Disjoint scratch ∧
    48 ≤ s.sp.toNat ∧ stack.Disjoint pw ∧ stack.Disjoint salt ∧ stack.Disjoint out ∧
    stack.Disjoint scratch ∧
    (s.gpr .x0).toNat + (s.gpr .x1).toNat ≤ 2 ^ 64 ∧ (s.gpr .x2).toNat + (s.gpr .x3).toNat ≤ 2 ^ 64 ∧
    (s.gpr .x5).toNat + (s.gpr .x6).toNat ≤ 2 ^ 64 ∧ (s.gpr .x7).toNat + 2048 ≤ 2 ^ 64 ∧
    0 < ((s.gpr .x4).setWidth 32).toNat ∧ (s.gpr .x6).toNat ≤ (2 ^ 32 - 1) * 32
  post s s' :=
    Spec.Pbkdf2.pbkdf2HmacSha256 (bytesAt s.mem (s.gpr .x0) (s.gpr .x1).toNat)
        (bytesAt s.mem (s.gpr .x2) (s.gpr .x3).toNat) ((s.gpr .x4).setWidth 32).toNat
        (s.gpr .x6).toNat =
      some (bytesAt s'.mem (s.gpr .x5) (s.gpr .x6).toNat)
  pub s₁ s₂ :=
    s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.gpr .x2 = s₂.gpr .x2 ∧
    s₁.gpr .x3 = s₂.gpr .x3 ∧ (s₁.gpr .x4).setWidth 32 = (s₂.gpr .x4).setWidth 32 ∧
    s₁.gpr .x5 = s₂.gpr .x5 ∧ s₁.gpr .x6 = s₂.gpr .x6 ∧ s₁.gpr .x7 = s₂.gpr .x7 ∧ s₁.sp = s₂.sp

end VG.Proof.Pbkdf2
