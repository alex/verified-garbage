import VerifiedGarbage.Spec.Hmac
import VerifiedGarbage.Proof.Sha256.X86.Contract

/-!
# HMAC-SHA-256: the x86 (32-bit) contracts

**Untrusted**: the contracts the proofs are written against; the artifacts are emitted with the shared contracts of `Spec/`, which imply these (`Contract.Implies`). The same functions as on x86-64
(`VerifiedGarbage/Spec/Hmac/X86_64.lean`): an HMAC-SHA-256 computation is
two SHA-256 streaming states (`VG.Spec.Sha256.Repr`), the inner one, which
absorbs `(K₀ ⊕ ipad) ‖ text`, and the outer one, which holds `K₀ ⊕ opad`.
`vg_hmac_sha256_init` sets them up from the key, the text is absorbed into
the inner state with `vg_sha256_update` (`VG.Proof.Sha256.updateX86`), and
`vg_hmac_sha256_finalize` computes the MAC.

Every argument is on the stack above the return address (cdecl). As in
`VG.Proof.Sha256.updateX86` and `VG.Proof.Sha256.finalizeX86`, the code may
overwrite its arguments, which the callee owns under cdecl.
`vg_hmac_sha256_init` has the x86-64 signature. `vg_hmac_sha256_finalize`
has the 32-bit ARM one (`VerifiedGarbage/Spec/Hmac/Arm.lean`), where the MAC
is written through an `out` pointer instead of being left in `scratch`, so
that the two 32-bit targets share one Rust signature; its arguments are then
those of `vg_sha256_finalize` with `outer` inserted after `inner`.
-/

namespace VG.Proof.Hmac

open Spec.Hmac

open Spec.Sha256 (Repr bytesAt)

open X86 in
/-- x86 (32-bit) contract for
`vg_hmac_sha256_init(inner: *mut [u8; 96], outer: *mut [u8; 96], key: *const u8, key_len: usize, scratch: *mut [u64; 20])`,
whose arguments are on the stack (cdecl), for a key of at most 64 bytes (the
SHA-256 block size): makes the streaming state at `inner` represent
`K₀ ⊕ ipad` and the one at `outer` represent `K₀ ⊕ opad`, for the key `K₀`
made of the `key_len` bytes at `key`.

The code may read `key` (`key_len` bytes), and read and write the arguments
(20 bytes above the return address, whose contents on exit are unspecified),
`inner` and `outer` (96 bytes each) and `scratch` (160 bytes, whose contents
on exit are unspecified). The writable buffers may not overlap each other,
the key or the return address, and nothing may wrap around the end of the
(32-bit) address space. `esp`, the pointers and `key_len` are public; the
key is secret. -/
def initSha256X86 : Contract X86.isa where
  pre s :=
    let inner : Region := ⟨(arg s 0).setWidth 64, 96⟩
    let outer : Region := ⟨(arg s 1).setWidth 64, 96⟩
    let key : Region := ⟨(arg s 2).setWidth 64, (arg s 3).toNat⟩
    let scratch : Region := ⟨(arg s 4).setWidth 64, 160⟩
    let args : Region := ⟨argAddr s 0, 20⟩
    let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
    (arg s 3).toNat ≤ 64 ∧ s.rd = [key] ∧ s.wr = [inner, outer, scratch, args] ∧
    inner.Disjoint outer ∧ inner.Disjoint scratch ∧ outer.Disjoint scratch ∧
    args.Disjoint inner ∧ args.Disjoint outer ∧ args.Disjoint scratch ∧
    key.Disjoint inner ∧ key.Disjoint outer ∧ key.Disjoint scratch ∧ key.Disjoint args ∧
    ret.Disjoint inner ∧ ret.Disjoint outer ∧ ret.Disjoint scratch ∧
    (arg s 0).toNat + 96 ≤ 2 ^ 32 ∧ (arg s 1).toNat + 96 ≤ 2 ^ 32 ∧
    (arg s 2).toNat + (arg s 3).toNat ≤ 2 ^ 32 ∧ (arg s 4).toNat + 160 ≤ 2 ^ 32 ∧
    (s.gpr .esp).toNat + 24 ≤ 2 ^ 32
  post s s' :=
    let k0 := blockKey sha256 (bytesAt s.mem ((arg s 2).setWidth 64) (arg s 3).toNat)
    Repr s'.mem ((arg s 0).setWidth 64) (xorPad k0 ipad) ∧
      Repr s'.mem ((arg s 1).setWidth 64) (xorPad k0 opad)
  pub s₁ s₂ :=
    s₁.gpr .esp = s₂.gpr .esp ∧ ∀ i < 5, arg s₁ i = arg s₂ i

open X86 in
/-- The 64-bit `count` argument of `vg_hmac_sha256_finalize`: its arguments
2 (the low word) and 3 (the high word). -/
def countFinalizeX86 (s : X86.State) : BitVec 64 := arg s 3 ++ arg s 2

open X86 in
/-- x86 (32-bit) contract for
`vg_hmac_sha256_finalize(inner: *mut [u8; 96], outer: *const [u8; 96], count: u64, out: *mut [u8; 32], scratch: *mut [u64; 30])`,
whose arguments are on the stack (cdecl: `inner`, `outer`, the low and high
words of `count`, `out`, `scratch`): if, for a 64-byte key `K₀` and a text,
the streaming state at `inner` represents `(K₀ ⊕ ipad) ‖ text`, of `count`
bytes (modulo 2⁶⁴), and the one at `outer` represents `K₀ ⊕ opad`, writes the
HMAC-SHA-256 of the text under `K₀` to `out`.

The code may read `outer` (96 bytes), and read and write the arguments (24
bytes above the return address, whose contents on exit are unspecified),
`inner` (96 bytes, whose contents on exit are unspecified), `out` (32 bytes)
and `scratch` (240 bytes, whose contents on exit are unspecified). The
writable buffers may not overlap each other, `outer` or the return address,
and nothing may wrap around the end of the (32-bit) address space. `esp`,
the pointers and `count` are public; the states are secret. -/
def finalizeSha256X86 : Contract X86.isa where
  pre s :=
    let inner : Region := ⟨(arg s 0).setWidth 64, 96⟩
    let outer : Region := ⟨(arg s 1).setWidth 64, 96⟩
    let out : Region := ⟨(arg s 4).setWidth 64, 32⟩
    let scratch : Region := ⟨(arg s 5).setWidth 64, 240⟩
    let args : Region := ⟨argAddr s 0, 24⟩
    let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
    s.rd = [outer] ∧ s.wr = [inner, out, scratch, args] ∧
    inner.Disjoint out ∧ inner.Disjoint scratch ∧ out.Disjoint scratch ∧
    args.Disjoint inner ∧ args.Disjoint out ∧ args.Disjoint scratch ∧
    outer.Disjoint inner ∧ outer.Disjoint out ∧ outer.Disjoint scratch ∧ outer.Disjoint args ∧
    ret.Disjoint inner ∧ ret.Disjoint out ∧ ret.Disjoint scratch ∧
    (arg s 0).toNat + 96 ≤ 2 ^ 32 ∧ (arg s 1).toNat + 96 ≤ 2 ^ 32 ∧
    (arg s 4).toNat + 32 ≤ 2 ^ 32 ∧ (arg s 5).toNat + 240 ≤ 2 ^ 32 ∧
    (s.gpr .esp).toNat + 28 ≤ 2 ^ 32
  post s s' := ∀ k0 text, k0.length = 64 →
    Repr s.mem ((arg s 0).setWidth 64) (xorPad k0 ipad ++ text) →
    countFinalizeX86 s = BitVec.ofNat 64 (64 + text.length) →
    Repr s.mem ((arg s 1).setWidth 64) (xorPad k0 opad) →
    bytesAt s'.mem ((arg s 4).setWidth 64) 32 = hmacBlockKey sha256 k0 text
  pub s₁ s₂ :=
    s₁.gpr .esp = s₂.gpr .esp ∧ ∀ i < 6, arg s₁ i = arg s₂ i

end VG.Proof.Hmac
