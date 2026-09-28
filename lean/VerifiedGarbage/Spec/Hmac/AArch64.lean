import VerifiedGarbage.Spec.Hmac
import VerifiedGarbage.Spec.Sha256.AArch64

/-!
# HMAC-SHA-256: the AArch64 contracts

**Trusted** (as every file in `Spec/`). The same functions as on x86-64
(`VerifiedGarbage/Spec/Hmac/X86_64.lean`), with the same Rust signatures: an
HMAC-SHA-256 computation is two SHA-256 streaming states
(`VG.Spec.Sha256.Repr`), the inner one, which absorbs `(K₀ ⊕ ipad) ‖ text`,
and the outer one, which holds `K₀ ⊕ opad`. `vg_hmac_sha256_init` sets them
up from the key, the text is absorbed into the inner state with
`vg_sha256_update` (`VG.Spec.Sha256.updateAArch64`), and
`vg_hmac_sha256_finalize` computes the MAC.

The arguments are in `x0`–`x4` (AAPCS64), and `bl` leaves the return address
in `x30` rather than on the stack, so unlike on x86-64 there is no return
address for the regions to avoid.
-/

namespace VG.Spec.Hmac

open Sha256 (Repr bytesAt)

open AArch64 in
/-- AArch64 contract for
`vg_hmac_sha256_init(inner: *mut [u8; 96], outer: *mut [u8; 96], key: *const u8, key_len: usize, scratch: *mut [u64; 20])`,
for a key of at most 64 bytes (the SHA-256 block size): makes the streaming
state at `inner` represent `K₀ ⊕ ipad` and the one at `outer` represent
`K₀ ⊕ opad`, for the key `K₀` made of the `key_len` bytes at `key`.

The code may read `key` (`key_len` bytes) and read and write `inner` and
`outer` (96 bytes each) and `scratch` (160 bytes, whose contents on exit are
unspecified). These may not overlap each other. The pointers and `key_len`
are public; the key is secret. -/
def initSha256AArch64 : Contract AArch64.isa where
  pre s :=
    let inner : Region := ⟨s.gpr .x0, 96⟩
    let outer : Region := ⟨s.gpr .x1, 96⟩
    let key : Region := ⟨s.gpr .x2, (s.gpr .x3).toNat⟩
    let scratch : Region := ⟨s.gpr .x4, 160⟩
    (s.gpr .x3).toNat ≤ 64 ∧ s.rd = [key] ∧ s.wr = [inner, outer, scratch] ∧
    inner.Disjoint outer ∧ inner.Disjoint scratch ∧ outer.Disjoint scratch ∧
    key.Disjoint inner ∧ key.Disjoint outer ∧ key.Disjoint scratch
  post s s' :=
    let k0 := blockKey sha256 (bytesAt s.mem (s.gpr .x2) (s.gpr .x3).toNat)
    Repr s'.mem (s.gpr .x0) (xorPad k0 ipad) ∧ Repr s'.mem (s.gpr .x1) (xorPad k0 opad)
  pub s₁ s₂ :=
    s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.gpr .x2 = s₂.gpr .x2 ∧
    s₁.gpr .x3 = s₂.gpr .x3 ∧ s₁.gpr .x4 = s₂.gpr .x4

open AArch64 in
/-- AArch64 contract for
`vg_hmac_sha256_finalize(inner: *mut [u8; 96], outer: *const [u8; 96], count: u64, scratch: *mut [u64; 30])`:
if, for a 64-byte key `K₀` and a text, the streaming state at `inner`
represents `(K₀ ⊕ ipad) ‖ text`, of `count` bytes (modulo 2⁶⁴), and the one at
`outer` represents `K₀ ⊕ opad`, leaves the HMAC-SHA-256 of the text under
`K₀` in bytes 176 to 207 of `scratch`.

The MAC is left in `scratch`, as on x86-64, so that both targets share one
Rust signature (and one Rust wrapper).

The code may read `outer` (96 bytes), and read and write `inner` (96 bytes,
whose contents on exit are unspecified) and `scratch` (240 bytes, whose
contents on exit are unspecified apart from the MAC). These may not overlap
each other. The pointers and `count` are public; the states are secret. -/
def finalizeSha256AArch64 : Contract AArch64.isa where
  pre s :=
    let inner : Region := ⟨s.gpr .x0, 96⟩
    let outer : Region := ⟨s.gpr .x1, 96⟩
    let scratch : Region := ⟨s.gpr .x3, 240⟩
    s.rd = [outer] ∧ s.wr = [inner, scratch] ∧
    inner.Disjoint outer ∧ inner.Disjoint scratch ∧ outer.Disjoint scratch
  post s s' := ∀ k0 text, k0.length = 64 →
    Repr s.mem (s.gpr .x0) (xorPad k0 ipad ++ text) →
    s.gpr .x2 = BitVec.ofNat 64 (64 + text.length) →
    Repr s.mem (s.gpr .x1) (xorPad k0 opad) →
    bytesAt s'.mem (s.gpr .x3 + 176) 32 = hmacBlockKey sha256 k0 text
  pub s₁ s₂ :=
    s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.gpr .x2 = s₂.gpr .x2 ∧
    s₁.gpr .x3 = s₂.gpr .x3

end VG.Spec.Hmac
