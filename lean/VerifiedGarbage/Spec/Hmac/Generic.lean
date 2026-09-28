import VerifiedGarbage.Spec.Hmac
import VerifiedGarbage.Spec.Sha256
import VerifiedGarbage.Spec.Sha1
import VerifiedGarbage.Spec.Md5
import VerifiedGarbage.Spec.Sha512
import VerifiedGarbage.TCB.Artifact

/-!
# HMAC over any streaming hash function: the contracts, on every target

**Trusted** (as every file in `Spec/`). An HMAC computation with the hash
function `H` is two streaming states of `H`: the inner one, which absorbs
`(K₀ ⊕ ipad) ‖ text`, and the outer one, which holds `K₀ ⊕ opad`. `init`
sets them up from the key, the text is absorbed into the inner state with
`H`'s own `update`, and `finalize` computes the MAC. These are the contracts
of HMAC-SHA-256 (`Spec/Hmac/Contract.lean`) with the hash function a
parameter (`StreamingHash`), so that one implementation, calling the
verified streaming functions of `H`, serves every hash function.

`finalize` writes the MAC through an `out` pointer on every target.

`A` is the target's calling convention. The signatures fix where the
arguments are, the memory each function may access, disjointness, and that
the pointers and lengths are public (see `TCB/Sig.lean`); the contracts add
the rest. `scratch` is the number of 64-bit words of working space, which
depends on the implementation (it holds the working space of the functions
it calls); `stack` is the number of bytes of stack below the stack pointer
that an implementation's calls use (see `Sig.contract`). The functions may
overwrite their arguments passed in memory, where the calling convention
allows it (`writeArgs`), to pass arguments to the functions they call.
-/

namespace VG.Spec.Hmac

open Sha256 (bytesAt)

/-- A hash function with a streaming (incremental) implementation, as the
HMAC and PBKDF2 contracts use it: the hash function itself, the size in
bytes of its streaming state and of its digest, and what it means for the
streaming state at an address to represent a message (the `Repr` of its
`init`, `update` and `finalize` contracts). -/
structure StreamingHash where
  H : HashFunction
  stateBytes : Nat
  digestBytes : Nat
  Repr : Mem → Addr → List Byte → Prop

/-- SHA-256: the 96-byte streaming state of `Spec/Sha256/Contract.lean`. -/
def sha256S : StreamingHash := ⟨sha256, 96, 32, Sha256.Repr⟩

/-- SHA-1: the 84-byte streaming state of `Spec/Sha1/Contract.lean`. -/
def sha1S : StreamingHash := ⟨sha1, 84, 20, Sha1.Repr⟩

/-- MD5: the 80-byte streaming state of `Spec/Md5/Contract.lean`. -/
def md5S : StreamingHash := ⟨md5, 80, 16, Md5.Repr⟩

/-- SHA-384: the 192-byte streaming state of `Spec/Sha512/Contract.lean`,
from SHA-384's initial hash value. -/
def sha384S : StreamingHash := ⟨sha384, 192, 48, Sha512.Repr Sha512.H0_384⟩

/-- SHA-512: as SHA-384, from SHA-512's initial hash value. -/
def sha512S : StreamingHash := ⟨sha512, 192, 64, Sha512.Repr Sha512.H0_512⟩

/-- SHA-512/224: as SHA-384, from SHA-512/224's initial hash value. -/
def sha512_224S : StreamingHash := ⟨sha512_224, 192, 28, Sha512.Repr Sha512.H0_512_224⟩

/-- SHA-512/256: as SHA-384, from SHA-512/256's initial hash value. -/
def sha512_256S : StreamingHash := ⟨sha512_256, 192, 32, Sha512.Repr Sha512.H0_512_256⟩

variable (S : StreamingHash) (scratch : Nat)

/-- `vg_hmac_<hash>_init(inner: *mut [u8; S], outer: *mut [u8; S], key: *const u8, key_len: usize, scratch: *mut [u64; W])`,
with `S` the size of the streaming state. `scratch` is working space. -/
def initSig : Sig where
  params := [("inner", .array true .u8 S.stateBytes), ("outer", .array true .u8 S.stateBytes),
    ("key", .slice false .u8 "key_len"), ("scratch", .array true .u64 scratch)]

/-- For a key of at most the block size of `H`: makes the streaming state at
`inner` represent `K₀ ⊕ ipad` and the one at `outer` represent `K₀ ⊕ opad`,
for the key `K₀` made of the `key_len` bytes at `key`. The key is secret. -/
def initContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  (initSig S scratch).contract A
    (pre := fun _inner _outer _key keyLen _scratch _ => keyLen.toNat ≤ S.H.blockSize)
    (post := fun inner outer key keyLen _scratch m m' _ =>
      let k0 := blockKey S.H (bytesAt m key keyLen.toNat)
      S.Repr m' inner (xorPad k0 ipad) ∧ S.Repr m' outer (xorPad k0 opad))
    (writeArgs := true)
    (stack := stack)

/-- `vg_hmac_<hash>_finalize(inner: *mut [u8; S], outer: *const [u8; S], count: u64, out: *mut [u8; D], scratch: *mut [u64; W])`,
with `S` the size of the streaming state and `D` that of the digest. `count`
is public; `inner` is left unspecified, and `scratch` is working space. -/
def finalizeSig : Sig where
  params := [("inner", .array true .u8 S.stateBytes), ("outer", .array false .u8 S.stateBytes),
    ("count", .int .u64 true), ("out", .array true .u8 S.digestBytes),
    ("scratch", .array true .u64 scratch)]

/-- If, for a key `K₀` of the block size of `H` and a text of fewer than
2⁶⁴ bytes with the key, the streaming state at `inner` represents
`(K₀ ⊕ ipad) ‖ text`, of `count` bytes (modulo 2⁶⁴), and the one at `outer`
represents `K₀ ⊕ opad`, writes the HMAC of the text under `K₀` to `out`. The
states are secret. -/
def finalizeContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  (finalizeSig S scratch).contract A (post := fun inner outer count out _scratch m m' _ =>
    ∀ k0 text, k0.length = S.H.blockSize → k0.length + text.length < 2 ^ 64 →
      S.Repr m inner (xorPad k0 ipad ++ text) →
      count = BitVec.ofNat 64 (S.H.blockSize + text.length) → S.Repr m outer (xorPad k0 opad) →
      bytesAt m' out S.digestBytes = hmacBlockKey S.H k0 text)
    (writeArgs := true)
    (stack := stack)

end VG.Spec.Hmac
