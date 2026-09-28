import VerifiedGarbage.Spec.ChaCha20Poly1305
import VerifiedGarbage.TCB.Artifact

/-!
# ChaCha20-Poly1305: the contracts, on every target

**Trusted** (as every file in `Spec/`). The contracts of the one-shot AEAD
functions, in terms of `Spec/ChaCha20Poly1305.lean`, for any target: `A` is
the target's calling convention. The signatures fix where the arguments are,
the memory each function may access, disjointness, and that the pointers and
lengths are public (see `TCB/Sig.lean`); the contracts add the rest. The key,
the nonce, the additional data, the data and the tags are secret.

The functions are composed in assembly from the ChaCha20 and Poly1305
primitives, which they call. So that every argument is passed in a register
on every target, the key, the nonce and the tag are passed in a context:

* bytes 0–31: the key;
* bytes 32–43: the nonce;
* bytes 48–63: the tag (written by `seal`, read by `open`);
* the rest: working space.

The data is encrypted or decrypted in place. Both functions may overwrite
their arguments passed in memory, where the calling convention allows it
(`writeArgs`), to pass arguments to the functions they call, and take the
number of bytes of stack below the stack pointer that their calls and frames
use (`stack`, see `Sig.contract`), which depends on the target.

The contracts do not limit the length of the data. Beyond RFC 8439's
`P_MAX`, 2³²-1 blocks, the ChaCha20 block counter wraps around (as in
`VG.Spec.ChaCha20.encrypt`) and the construction is no longer secure: the
caller must enforce `P_MAX`.
-/

namespace VG.Spec.ChaCha20Poly1305

open Poly1305 (bytesAt)

/-- `vg_chacha20_poly1305_seal(ctx: *mut [u64; 128], aad: *const u8, aad_len: usize, data: *mut u8, len: usize)`. -/
def sealSig : Sig where
  params := [("ctx", .array true .u64 128), ("aad", .slice false .u8 "aad_len"),
    ("data", .slice true .u8 "len")]

/-- With the key and the nonce in the context: encrypts the `len` bytes at
`data` in place, for the `aad_len` bytes of additional data at `aad`, and
writes the tag to bytes 48–63 of the context. -/
def sealContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  sealSig.contract A (post := fun ctx aad aadLen data len m m' _ =>
    encrypt (bytesAt m ctx 32) (bytesAt m (ctx + 32) 12) (bytesAt m aad aadLen.toNat)
        (bytesAt m data len.toNat) =
      (bytesAt m' data len.toNat, bytesAt m' (ctx + 48) 16))
    (writeArgs := true)
    (stack := stack)

/-- `vg_chacha20_poly1305_open(ctx: *mut [u64; 128], aad: *const u8, aad_len: usize, data: *mut u8, len: usize) -> u32`. -/
def openSig : Sig where
  params := [("ctx", .array true .u64 128), ("aad", .slice false .u8 "aad_len"),
    ("data", .slice true .u8 "len")]
  ret := some .u32

/-- With the key, the nonce and the received tag in the context: if the
message (the `len` bytes of ciphertext at `data`, with the `aad_len` bytes of
additional data at `aad`) is authenticated, returns 1 and leaves the
plaintext at `data`; otherwise returns 0, and the bytes at `data` are
unspecified (the caller must not use them). -/
def openContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  openSig.contract A (post := fun ctx aad aadLen data len m m' r =>
    match decrypt (bytesAt m ctx 32) (bytesAt m (ctx + 32) 12) (bytesAt m aad aadLen.toNat)
        (bytesAt m data len.toNat) (bytesAt m (ctx + 48) 16) with
    | some pt => r = 1 ∧ bytesAt m' data len.toNat = pt
    | none => r = 0)
    (writeArgs := true)
    (stack := stack)

end VG.Spec.ChaCha20Poly1305
