import VerifiedGarbage.Spec.Ccm
import VerifiedGarbage.TCB.Artifact

/-!
# AES-CCM: the contracts, on every target

**Trusted** (as every file in `Spec/`). The contracts of one-shot AES-CCM
generation-encryption and decryption-verification, in terms of
`Spec/Ccm.lean`, for any target: `A` is the target's calling convention.
The signatures fix where the arguments are, the memory each function may
access, disjointness, and that the pointers, the lengths, the number of
rounds and the MAC length are public (see `TCB/Sig.lean`); the contracts
add the rest. Everything else (key schedules, nonces, associated data,
texts and tags) is secret.

All a caller keeps of a key is its key schedule, as `vg_aes_expand_key`
writes it (`VG.Spec.Aes.expandKeyContract`), with its number of rounds. The
functions compute with the cipher of the schedule they are given, for the
number of rounds they are given (`ctxCiph`): with the schedule of a key,
that is AES-CCM with that key (`ctxCiph_eq`).

* `vg_aes_ccm_seal` is generation-encryption (`encryptWith`): it encrypts
  the payload in place and writes the encrypted MAC of `tag_len` bytes,
  the tag (the ciphertext of §6.1 is the encrypted payload followed by the
  tag).
* `vg_aes_ccm_open` is decryption-verification (`decryptWith`): given the
  encrypted payload in place and the tag, it decrypts, and if the MAC is
  wrong overwrites the payload with zeros, so that it is never revealed
  (§6.2). Whether the MAC is right is public: `open` may leak it (it is the
  result), and nothing else secret.

The lengths are public, and the lengths of Appendix A.1 that the formatting
depends on are preconditions (`valid`): the MAC length `tag_len`, the nonce
length `nonce_len` and the payload's length `len < 2^(8q)` for
`q = 15 − nonce_len`, which the caller checks. The tag travels in the first
`tag_len` bytes of `work`, which is also working space, so that fewer
arguments are passed in memory; `work` has room for `vg_aes_ctr32`'s working
space (2048 bytes) and 512 bytes more.

Every contract takes the number of bytes of stack below the stack pointer
that an implementation's calls and frames use (`stack`, see `Sig.contract`),
0 for one that uses none; the functions may overwrite their arguments passed
in memory, where the calling convention allows it (`writeArgs`), to pass
arguments to the functions they call.
-/

namespace VG.Spec.Ccm

/-- `vg_aes_ccm_seal(schedule: *const [u8; 240], rounds: usize, nonce: *const u8, nonce_len: usize, aad: *const u8, aad_len: usize, data: *mut u8, len: usize, work: *mut [u64; 320], tag_len: usize)`,
and `vg_aes_ccm_open` with the same parameters, returning a `u32`. `rounds`
and `tag_len` are public; `work` is working space but for the tag. -/
def sealSig : Sig where
  params := [("schedule", .array false .u8 240), ("rounds", .int .usize true),
    ("nonce", .slice false .u8 "nonce_len"), ("aad", .slice false .u8 "aad_len"),
    ("data", .slice true .u8 "len"), ("work", .array true .u64 320),
    ("tag_len", .int .usize true)]

/-- `vg_aes_ccm_open`'s signature: `vg_aes_ccm_seal`'s, returning a `u32`. -/
def openSig : Sig := { sealSig with ret := some .u32 }

/-- For `rounds` of 10, 12 or 14, a MAC length `tag_len`, a nonce of
`nonce_len` bytes and `len` bytes of payload that Appendix A.1 allows, with
the key schedule in the first `16 (rounds + 1)` bytes at `schedule`:
encrypts the `len` bytes at `data` in place, with the nonce at `nonce` and
the `aad_len` bytes of associated data at `aad` (`encryptWith`), and writes
the encrypted MAC of `tag_len` bytes to the first `tag_len` bytes of
`work`. -/
def sealContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  sealSig.contract A
    (pre := fun _schedule rounds _nonce nonceLen _aad aadLen _data len _work tagLen _ =>
      (rounds.toNat = 10 ∨ rounds.toNat = 12 ∨ rounds.toNat = 14) ∧
        valid tagLen.toNat nonceLen.toNat aadLen.toNat len.toNat)
    (post := fun schedule rounds nonce nonceLen aad aadLen data len work tagLen m m' _ =>
      encryptWith (ctxCiph m schedule rounds.toNat) tagLen.toNat
          (Aes.bytesAt m nonce nonceLen.toNat) (Aes.bytesAt m data len.toNat)
          (Aes.bytesAt m aad aadLen.toNat) =
        (Aes.bytesAt m' data len.toNat, Aes.bytesAt m' work tagLen.toNat))
    (writeArgs := true)
    (stack := stack)

/-- `vg_aes_ccm_seal` on every target. -/
def sealApi : Api where
  module := "aes_ccm"
  name := "vg_aes_ccm_seal"
  sig := sealSig
  writeArgs := true
  contracts := some fun A stack => sealContract A stack
  summary := "AES-CCM generation-encryption (NIST SP 800-38C §6.1, with the formatting and \
    counter generation of its Appendix A): with the key schedule in the first \
    `16 * (rounds + 1)` bytes of `*schedule`, as `vg_aes_expand_key` writes it, encrypts the \
    `len` bytes of payload at `data` in place, under the `nonce_len`-byte nonce at `nonce`, and \
    writes the encrypted MAC (`T ⊕ MSB_Tlen(S₀)`) of `tag_len` bytes, of the payload and the \
    `aad_len` bytes of associated data at `aad`, to the first `tag_len` bytes of `*work`. The \
    ciphertext of §6.1 is the encrypted payload followed by it. The rest of `*work` is working \
    space, unspecified on return.\n\n\
    Contract: `VG.Spec.Ccm.sealContract`. Constant time: only the pointers, `rounds`, the \
    lengths and `tag_len` may affect timing, not the key schedule, the nonce, the associated \
    data or the payload."
  safety := [
    "`rounds` must be 10, 12 or 14.",
    "`tag_len` must be 4, 6, 8, 10, 12, 14 or 16, and `nonce_len` from 7 to 13 \
      (Appendix A.1).",
    "`len` must be less than `2^(8 * (15 - nonce_len))` (Appendix A.1)."]

/-- For `rounds` of 10, 12 or 14, a MAC length `tag_len`, a nonce of
`nonce_len` bytes and `len` bytes of payload that Appendix A.1 allows, with
the key schedule in the first `16 (rounds + 1)` bytes at `schedule` and the
received tag (the encrypted MAC) in the first `tag_len` bytes of `work`: if
the MAC is right for the `len` bytes of encrypted payload at `data`, the
nonce at `nonce` and the `aad_len` bytes of associated data at `aad`
(`decryptWith`), returns 1 and leaves the payload at `data`; otherwise
returns 0 and leaves zeros at `data`. May leak which (`decryptWith`'s
outcome). -/
def openContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  openSig.contract A
    (pre := fun _schedule rounds _nonce nonceLen _aad aadLen _data len _work tagLen _ =>
      (rounds.toNat = 10 ∨ rounds.toNat = 12 ∨ rounds.toNat = 14) ∧
        valid tagLen.toNat nonceLen.toNat aadLen.toNat len.toNat)
    (post := fun schedule rounds nonce nonceLen aad aadLen data len work tagLen m m' r =>
      match decryptWith (ctxCiph m schedule rounds.toNat) tagLen.toNat
          (Aes.bytesAt m nonce nonceLen.toNat) (Aes.bytesAt m data len.toNat)
          (Aes.bytesAt m aad aadLen.toNat) (Aes.bytesAt m work tagLen.toNat) with
      | some pt => r = 1 ∧ Aes.bytesAt m' data len.toNat = pt
      | none => r = 0 ∧ Aes.bytesAt m' data len.toNat = zeros len.toNat)
    (writeArgs := true)
    (stack := stack)
    (leak := some fun schedule rounds nonce nonceLen aad aadLen data len work tagLen m =>
      [if (decryptWith (ctxCiph m schedule rounds.toNat) tagLen.toNat
          (Aes.bytesAt m nonce nonceLen.toNat) (Aes.bytesAt m data len.toNat)
          (Aes.bytesAt m aad aadLen.toNat) (Aes.bytesAt m work tagLen.toNat)).isSome
        then 1 else 0])

/-- `vg_aes_ccm_open` on every target. -/
def openApi : Api where
  module := "aes_ccm"
  name := "vg_aes_ccm_open"
  sig := openSig
  writeArgs := true
  contracts := some fun A stack => openContract A stack
  summary := "AES-CCM decryption-verification (NIST SP 800-38C §6.2, with the formatting and \
    counter generation of its Appendix A): with the key schedule in the first \
    `16 * (rounds + 1)` bytes of `*schedule`, as `vg_aes_expand_key` writes it, and the \
    received encrypted MAC of `tag_len` bytes (the last `tag_len` bytes of the ciphertext) in \
    the first `tag_len` bytes of `*work`, decrypts the `len` bytes of encrypted payload at \
    `data` in place, under the `nonce_len`-byte nonce at `nonce`, and returns 1 if the MAC is \
    that of the payload and the `aad_len` bytes of associated data at `aad`; otherwise returns \
    0 and overwrites the `len` bytes at `data` with zeros. The rest of `*work` is working \
    space, unspecified on return. The MACs are compared without a branch.\n\n\
    Contract: `VG.Spec.Ccm.openContract`. Constant time but for the result: only the pointers, \
    `rounds`, the lengths, `tag_len` and whether the function returns 1 or 0 may affect timing, \
    not the key schedule, the nonce, the associated data, the data or the tag."
  safety := [
    "`rounds` must be 10, 12 or 14.",
    "`tag_len` must be 4, 6, 8, 10, 12, 14 or 16, and `nonce_len` from 7 to 13 \
      (Appendix A.1).",
    "`len` must be less than `2^(8 * (15 - nonce_len))` (Appendix A.1)."]

end VG.Spec.Ccm
