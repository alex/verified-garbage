import VerifiedGarbage.Spec.Hmac
import VerifiedGarbage.Spec.Sha256.X86_64

/-!
# HMAC-SHA-256: the x86-64 contracts

**Trusted** (as every file in `Spec/`). An HMAC-SHA-256 computation is two
SHA-256 streaming states (`VG.Spec.Sha256.Repr`): the inner one, which
absorbs `(K₀ ⊕ ipad) ‖ text`, and the outer one, which holds `K₀ ⊕ opad`.
`vg_hmac_sha256_init` sets them up from the key, the text is absorbed into
the inner state with `vg_sha256_update` (its contract,
`VG.Spec.Sha256.updateX86_64`, is all that is needed), and
`vg_hmac_sha256_finalize` computes the MAC.
-/

namespace VG.Spec.Hmac

open Sha256 (Repr bytesAt)

open X86_64 in
/-- x86-64 contract for
`vg_hmac_sha256_init(inner: *mut [u8; 96], outer: *mut [u8; 96], key: *const u8, key_len: usize, scratch: *mut [u64; 20])`,
for a key of at most 64 bytes (the SHA-256 block size): makes the streaming
state at `inner` represent `K₀ ⊕ ipad` and the one at `outer` represent
`K₀ ⊕ opad`, for the key `K₀` made of the `key_len` bytes at `key`.

The code may read `key` (`key_len` bytes) and read and write `inner` and
`outer` (96 bytes each) and `scratch` (160 bytes, whose contents on exit are
unspecified). These may not overlap each other, nor the return address on
the stack. The pointers and `key_len` are public; the key is secret. -/
def initSha256X86_64 : Contract X86_64.isa where
  pre s :=
    let inner : Region := ⟨s.gpr .rdi, 96⟩
    let outer : Region := ⟨s.gpr .rsi, 96⟩
    let key : Region := ⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩
    let scratch : Region := ⟨s.gpr .r8, 160⟩
    let ret : Region := ⟨s.gpr .rsp, 8⟩
    (s.gpr .rcx).toNat ≤ 64 ∧ s.rd = [key] ∧ s.wr = [inner, outer, scratch] ∧
    inner.Disjoint outer ∧ inner.Disjoint scratch ∧ outer.Disjoint scratch ∧
    key.Disjoint inner ∧ key.Disjoint outer ∧ key.Disjoint scratch ∧
    ret.Disjoint inner ∧ ret.Disjoint outer ∧ ret.Disjoint scratch
  post s s' :=
    let k0 := blockKey sha256 (bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat)
    Repr s'.mem (s.gpr .rdi) (xorPad k0 ipad) ∧ Repr s'.mem (s.gpr .rsi) (xorPad k0 opad)
  pub s₁ s₂ :=
    s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rdx = s₂.gpr .rdx ∧
    s₁.gpr .rcx = s₂.gpr .rcx ∧ s₁.gpr .r8 = s₂.gpr .r8

open X86_64 in
/-- x86-64 contract for
`vg_hmac_sha256_finalize(inner: *mut [u8; 96], outer: *const [u8; 96], count: u64, scratch: *mut [u64; 30])`:
if, for a 64-byte key `K₀` and a text, the streaming state at `inner`
represents `(K₀ ⊕ ipad) ‖ text`, of `count` bytes (modulo 2⁶⁴), and the one at
`outer` represents `K₀ ⊕ opad`, leaves the HMAC-SHA-256 of the text under
`K₀` in bytes 176 to 207 of `scratch`.

The MAC is left in `scratch` rather than written through a pointer of its
own so that the code can address every region from the two pointers it
keeps in registers across the inlined SHA-256 finalizations.

The code may read `outer` (96 bytes), and read and write `inner` (96 bytes,
whose contents on exit are unspecified) and `scratch` (240 bytes, whose
contents on exit are unspecified apart from the MAC). These may not overlap
each other, nor the return address on the stack. The pointers and `count`
are public; the states are secret. -/
def finalizeSha256X86_64 : Contract X86_64.isa where
  pre s :=
    let inner : Region := ⟨s.gpr .rdi, 96⟩
    let outer : Region := ⟨s.gpr .rsi, 96⟩
    let scratch : Region := ⟨s.gpr .rcx, 240⟩
    let ret : Region := ⟨s.gpr .rsp, 8⟩
    s.rd = [outer] ∧ s.wr = [inner, scratch] ∧
    inner.Disjoint outer ∧ inner.Disjoint scratch ∧ outer.Disjoint scratch ∧
    ret.Disjoint inner ∧ ret.Disjoint outer ∧ ret.Disjoint scratch
  post s s' := ∀ k0 text, k0.length = 64 →
    Repr s.mem (s.gpr .rdi) (xorPad k0 ipad ++ text) →
    s.gpr .rdx = BitVec.ofNat 64 (64 + text.length) →
    Repr s.mem (s.gpr .rsi) (xorPad k0 opad) →
    bytesAt s'.mem (s.gpr .rcx + 176) 32 = hmacBlockKey sha256 k0 text
  pub s₁ s₂ :=
    s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rdx = s₂.gpr .rdx ∧
    s₁.gpr .rcx = s₂.gpr .rcx

end VG.Spec.Hmac
