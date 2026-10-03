import VerifiedGarbage.Spec.GcmSiv
import VerifiedGarbage.TCB.Artifact

/-!
# AES-GCM-SIV: the contracts, on every target

**Trusted** (as every file in `Spec/`). The contracts of one-shot
AES-GCM-SIV encryption and decryption, in terms of `Spec/GcmSiv.lean`, for
any target: `A` is the target's calling convention. The signatures fix
where the arguments are, the memory each function may access,
disjointness, and that the pointers, the lengths and the number of rounds
are public (see `TCB/Sig.lean`); the contracts add the rest. Everything else
(key schedules, nonces, additional data, texts and tags) is secret.

AES-GCM-SIV derives its keys from the key-generating key per nonce (RFC 8452
§4), so all a caller keeps of a key is the key schedule of the
key-generating key, as `vg_aes_expand_key` writes it
(`VG.Spec.Aes.expandKeyContract`), with its number of rounds: 10 for a
16-byte key, 14 for a 32-byte key. The functions compute with the cipher of
the schedule they are given, for the number of rounds they are given
(`ctxCiph`, `keyLen`): with the schedule of a key, that is AES-GCM-SIV with
that key (`encryptWith_ctx`, `decryptWith_ctx`).

* `vg_aes_gcm_siv_seal` is encryption (`encryptWith`): it encrypts the data
  in place and writes the 16-byte tag.
* `vg_aes_gcm_siv_open` is decryption (`decryptWith`): given the encrypted
  plaintext in place and the tag, it decrypts, and if the tag is wrong
  overwrites the data with zeros, so that the unauthenticated plaintext is
  never released (§5). Whether the tag is right is public: `open` may leak
  it (it is the result), and nothing else secret.

The functions check no length (which are public): the caller checks the
lengths of §6 (`supported`: at most 2³⁶ bytes of plaintext and of
additional data). The nonce is 12 bytes (§6), the tag 16. The tag travels in
the first 16 bytes of `work`, which is also working space, so that fewer
arguments are passed in memory; `work` has room for `vg_aes_ctr32`'s working
space (2048 bytes), the message-encryption key's schedule and
`vg_aes_expand_key`'s working space, and more.

Every contract takes the number of bytes of stack below the stack pointer
that an implementation's calls and frames use (`stack`, see `Sig.contract`),
0 for one that uses none; the functions may overwrite their arguments passed
in memory, where the calling convention allows it (`writeArgs`), to pass
arguments to the functions they call.
-/

namespace VG.Spec.GcmSiv

/-- `vg_aes_gcm_siv_seal(schedule: *const [u8; 240], rounds: usize, nonce: *const [u8; 12], aad: *const u8, aad_len: usize, data: *mut u8, len: usize, work: *mut [u64; 512])`.
`rounds` is public; `work` is working space but for the tag it returns. -/
def sealSig : Sig where
  params := [("schedule", .array false .u8 240), ("rounds", .int .usize true),
    ("nonce", .array false .u8 12), ("aad", .slice false .u8 "aad_len"),
    ("data", .slice true .u8 "len"), ("work", .array true .u64 512)]

/-- For `rounds` of 10 or 14, with the key schedule of the key-generating key
in the first `16 (rounds + 1)` bytes at `schedule`: encrypts the `len` bytes
at `data` in place, with the 12-byte nonce at `nonce` and the `aad_len`
bytes of additional data at `aad` (`encryptWith`), and writes the 16-byte
tag to the first 16 bytes of `work`. -/
def sealContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  sealSig.contract A
    (pre := fun _schedule rounds _nonce _aad _aadLen _data _len _work _ =>
      rounds.toNat = 10 ∨ rounds.toNat = 14)
    (post := fun schedule rounds nonce aad aadLen data len work m m' _ =>
      encryptWith (ctxCiph m schedule rounds.toNat) (keyLen rounds.toNat) (Aes.bytesAt m nonce 12)
          (Aes.bytesAt m data len.toNat) (Aes.bytesAt m aad aadLen.toNat) =
        (Aes.bytesAt m' data len.toNat, Aes.bytesAt m' work 16))
    (writeArgs := true)
    (stack := stack)

/-- `vg_aes_gcm_siv_seal` on every target. -/
def sealApi : Api where
  module := "aes_gcm_siv"
  name := "vg_aes_gcm_siv_seal"
  sig := sealSig
  writeArgs := true
  contracts := some fun A stack => sealContract A stack
  summary := "AES-GCM-SIV authenticated encryption (RFC 8452 §4): with the key schedule of the \
    key-generating key in the first `16 * (rounds + 1)` bytes of `*schedule`, as \
    `vg_aes_expand_key` writes it (`rounds` is 10 for a 16-byte key, 14 for a 32-byte key), \
    encrypts the `len` bytes at `data` in place, under the 12-byte nonce `*nonce`, and writes \
    the 16-byte tag of the plaintext and the `aad_len` bytes of additional data at `aad` to the \
    first 16 bytes of `*work`. The RFC's ciphertext is the encrypted data followed by the tag. \
    The rest of `*work` is working space, unspecified on return.\n\n\
    The function checks no length. AES-GCM-SIV is defined for at most `2^36` bytes of data and \
    at most `2^36` bytes of additional data (§6), which the caller must ensure.\n\n\
    Contract: `VG.Spec.GcmSiv.sealContract`. Constant time: only the pointers, `rounds` and the \
    lengths may affect timing, not the key schedule, the nonce, the additional data or the data."
  safety := ["`rounds` must be 10 or 14."]

/-- `vg_aes_gcm_siv_open(schedule: *const [u8; 240], rounds: usize, nonce: *const [u8; 12], aad: *const u8, aad_len: usize, data: *mut u8, len: usize, work: *mut [u64; 512]) -> u32`.
`rounds` is public; `work` is working space but for the tag it is given. -/
def openSig : Sig where
  params := [("schedule", .array false .u8 240), ("rounds", .int .usize true),
    ("nonce", .array false .u8 12), ("aad", .slice false .u8 "aad_len"),
    ("data", .slice true .u8 "len"), ("work", .array true .u64 512)]
  ret := some .u32

/-- For `rounds` of 10 or 14, with the key schedule of the key-generating key
in the first `16 (rounds + 1)` bytes at `schedule` and the received tag in
the first 16 bytes of `work`: if the tag is right for the `len` bytes of
encrypted plaintext at `data`, the 12-byte nonce at `nonce` and the
`aad_len` bytes of additional data at `aad` (`decryptWith`), returns 1 and
leaves the plaintext at `data`; otherwise returns 0 and leaves zeros at
`data`. May leak which (`decryptWith`'s outcome). -/
def openContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  openSig.contract A
    (pre := fun _schedule rounds _nonce _aad _aadLen _data _len _work _ =>
      rounds.toNat = 10 ∨ rounds.toNat = 14)
    (post := fun schedule rounds nonce aad aadLen data len work m m' r =>
      match decryptWith (ctxCiph m schedule rounds.toNat) (keyLen rounds.toNat)
          (Aes.bytesAt m nonce 12) (Aes.bytesAt m data len.toNat) (Aes.bytesAt m aad aadLen.toNat)
          (Aes.bytesAt m work 16) with
      | some pt => r = 1 ∧ Aes.bytesAt m' data len.toNat = pt
      | none => r = 0 ∧ Aes.bytesAt m' data len.toNat = zeros len.toNat)
    (writeArgs := true)
    (stack := stack)
    (leak := some fun schedule rounds nonce aad aadLen data len work m =>
      [if (decryptWith (ctxCiph m schedule rounds.toNat) (keyLen rounds.toNat)
          (Aes.bytesAt m nonce 12) (Aes.bytesAt m data len.toNat) (Aes.bytesAt m aad aadLen.toNat)
          (Aes.bytesAt m work 16)).isSome
        then 1 else 0])

/-- `vg_aes_gcm_siv_open` on every target. -/
def openApi : Api where
  module := "aes_gcm_siv"
  name := "vg_aes_gcm_siv_open"
  sig := openSig
  writeArgs := true
  contracts := some fun A stack => openContract A stack
  summary := "AES-GCM-SIV authenticated decryption (RFC 8452 §5): with the key schedule of the \
    key-generating key in the first `16 * (rounds + 1)` bytes of `*schedule`, as \
    `vg_aes_expand_key` writes it (`rounds` is 10 for a 16-byte key, 14 for a 32-byte key), and \
    the received 16-byte tag in the first 16 bytes of `*work`, decrypts the `len` bytes of \
    encrypted plaintext at `data` in place, under the 12-byte nonce `*nonce`, and returns 1 if \
    the tag is that of the plaintext and the `aad_len` bytes of additional data at `aad`; \
    otherwise returns 0 and overwrites the `len` bytes at `data` with zeros. The rest of `*work` \
    is working space, unspecified on return. The tags are compared without a branch.\n\n\
    The function checks no length. AES-GCM-SIV is defined for at most `2^36` bytes of data and \
    at most `2^36` bytes of additional data (§6), which the caller must check.\n\n\
    Contract: `VG.Spec.GcmSiv.openContract`. Constant time but for the result: only the \
    pointers, `rounds`, the lengths and whether the function returns 1 or 0 may affect timing, \
    not the key schedule, the nonce, the additional data, the data or the tag."
  safety := ["`rounds` must be 10 or 14."]

end VG.Spec.GcmSiv
