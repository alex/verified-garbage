import VerifiedGarbage.Spec.Hmac
import VerifiedGarbage.Proof.Sha256.PPC64LE.Contract

/-!
# HMAC-SHA-256: the PPC64LE contracts

**Untrusted**: the contracts the proofs are written against; the artifacts are emitted with the shared contracts of `Spec/`, which imply these (`Contract.Implies`). The same functions as on x86-64
(`VerifiedGarbage/Spec/Hmac/Generic.lean`, `VG.Spec.Hmac.sha256I`), with the same Rust signatures: an
HMAC-SHA-256 computation is two SHA-256 streaming states
(`VG.Spec.Sha256.Repr`), the inner one, which absorbs `(K₀ ⊕ ipad) ‖ text`,
and the outer one, which holds `K₀ ⊕ opad`. `vg_hmac_sha256_init` sets them
up from the key, the text is absorbed into the inner state with
`vg_sha256_update` (`VG.Proof.Sha256.updatePPC64LE`), and
`vg_hmac_sha256_finalize` computes the MAC.

The arguments are in `r3`–`r7` (ELFv2), and `bl` leaves the return address
in the link register rather than on the stack, so unlike on x86-64 there is
no return address for the regions to avoid.
-/

namespace VG.Proof.Hmac

open Spec.Hmac

open Spec.Sha256 (Repr bytesAt)

open PPC64LE in
/-- PPC64LE contract for
`vg_hmac_sha256_init(inner: *mut [u8; 96], outer: *mut [u8; 96], key: *const u8, key_len: usize, scratch: *mut [u64; 20])`,
for a key of at most 64 bytes (the SHA-256 block size): makes the streaming
state at `inner` represent `K₀ ⊕ ipad` and the one at `outer` represent
`K₀ ⊕ opad`, for the key `K₀` made of the `key_len` bytes at `key`.

The code may read `key` (`key_len` bytes) and read and write `inner` and
`outer` (96 bytes each) and `scratch` (160 bytes, whose contents on exit are
unspecified). These may not overlap each other, nor the 48 bytes below the
stack pointer (the frame saving the link register), which do not wrap around. The
pointers and `key_len` are public; the key is secret. -/
def initSha256PPC64LE : Contract PPC64LE.isa where
  pre s :=
    let inner : Region := ⟨s.gpr .r3, 96⟩
    let outer : Region := ⟨s.gpr .r4, 96⟩
    let key : Region := ⟨s.gpr .r5, (s.gpr .r6).toNat⟩
    let scratch : Region := ⟨s.gpr .r7, 160⟩
    let stack : Region := ⟨s.sp - 48, 48⟩
    (s.gpr .r6).toNat ≤ 64 ∧ s.rd = [key] ∧ s.wr = [inner, outer, scratch] ∧
    inner.Disjoint outer ∧ inner.Disjoint scratch ∧ outer.Disjoint scratch ∧
    key.Disjoint inner ∧ key.Disjoint outer ∧ key.Disjoint scratch ∧
    48 ≤ s.sp.toNat ∧ stack.Disjoint inner ∧ stack.Disjoint outer ∧ stack.Disjoint key ∧
    stack.Disjoint scratch
  post s s' :=
    let k0 := blockKey sha256 (bytesAt s.mem (s.gpr .r5) (s.gpr .r6).toNat)
    Repr s'.mem (s.gpr .r3) (xorPad k0 ipad) ∧ Repr s'.mem (s.gpr .r4) (xorPad k0 opad)
  pub s₁ s₂ :=
    s₁.gpr .r3 = s₂.gpr .r3 ∧ s₁.gpr .r4 = s₂.gpr .r4 ∧ s₁.gpr .r5 = s₂.gpr .r5 ∧
    s₁.gpr .r6 = s₂.gpr .r6 ∧ s₁.gpr .r7 = s₂.gpr .r7 ∧ s₁.sp = s₂.sp

open PPC64LE in
/-- PPC64LE contract for
`vg_hmac_sha256_finalize(inner: *mut [u8; 96], outer: *const [u8; 96], count: u64, out: *mut [u8; 32], scratch: *mut [u64; 31])`:
if, for a 64-byte key `K₀` and a text, the streaming state at `inner`
represents `(K₀ ⊕ ipad) ‖ text`, of `count` bytes (modulo 2⁶⁴), and the one at
`outer` represents `K₀ ⊕ opad`, writes the HMAC-SHA-256 of the text under
`K₀` to `out`.

The code may read `outer` (96 bytes), and read and write `inner` (96 bytes,
whose contents on exit are unspecified), `out` (32 bytes) and `scratch` (248
bytes, whose contents on exit are unspecified). These may not overlap each
other, nor the 96 bytes below the stack pointer (the frames saving the link
register here and in `vg_sha256_finalize`), which do not wrap around. The
pointers and `count` are public; the states are secret. -/
def finalizeSha256PPC64LE : Contract PPC64LE.isa where
  pre s :=
    let inner : Region := ⟨s.gpr .r3, 96⟩
    let outer : Region := ⟨s.gpr .r4, 96⟩
    let out : Region := ⟨s.gpr .r6, 32⟩
    let scratch : Region := ⟨s.gpr .r7, 248⟩
    let stack : Region := ⟨s.sp - 96, 96⟩
    s.rd = [outer] ∧ s.wr = [inner, out, scratch] ∧
    inner.Disjoint outer ∧ inner.Disjoint out ∧ inner.Disjoint scratch ∧
    outer.Disjoint out ∧ outer.Disjoint scratch ∧ out.Disjoint scratch ∧
    96 ≤ s.sp.toNat ∧ stack.Disjoint inner ∧ stack.Disjoint outer ∧ stack.Disjoint out ∧
    stack.Disjoint scratch
  post s s' := ∀ k0 text, k0.length = 64 → k0.length + text.length < 2 ^ 64 →
    Repr s.mem (s.gpr .r3) (xorPad k0 ipad ++ text) →
    s.gpr .r5 = BitVec.ofNat 64 (64 + text.length) →
    Repr s.mem (s.gpr .r4) (xorPad k0 opad) →
    bytesAt s'.mem (s.gpr .r6) 32 = hmacBlockKey sha256 k0 text
  pub s₁ s₂ :=
    s₁.gpr .r3 = s₂.gpr .r3 ∧ s₁.gpr .r4 = s₂.gpr .r4 ∧ s₁.gpr .r5 = s₂.gpr .r5 ∧
    s₁.gpr .r6 = s₂.gpr .r6 ∧ s₁.gpr .r7 = s₂.gpr .r7 ∧ s₁.sp = s₂.sp

end VG.Proof.Hmac
