import VerifiedGarbage.Spec.Ocb
import VerifiedGarbage.TCB.Artifact

/-!
# AES-OCB: the contracts, on every target

**Trusted** (as every file in `Spec/`). The contracts of AES-OCB (OCB3), in
terms of `Spec/Ocb.lean`, for any target: `A` is the target's calling
convention. The signatures fix where the arguments are, the memory each
function may access, disjointness, and that the pointers, the lengths, the
number of rounds and the tag length are public (see `TCB/Sig.lean`); the
contracts add the rest. Everything else (keys, key contexts, nonces,
associated data, texts and tags) is secret.

* `vg_aes_ocb_init` writes a key context (`KeyRepr`): the key schedule and
  `L_* = ENCIPHER(K, zeros(128))`. The others read one, with its number of
  rounds, and compute with the ciphers of its key schedule and its `L_*`
  (`ctxCiph`, `ctxInv`, `ctxLstar`): with a context `vg_aes_ocb_init`
  wrote, that is AES-OCB with its key (`encryptWith_ctx`,
  `decryptWith_ctx`).
* `vg_aes_ocb_seal` is `OCB-ENCRYPT` (`encryptWith`): it encrypts the data in
  place and writes the tag of `tag_len` bytes.
* `vg_aes_ocb_open` is `OCB-DECRYPT` (`decryptWith`): given the encrypted
  data in place and the tag, it decrypts, and if the tag is wrong
  overwrites the data with zeros, so that the unauthenticated plaintext is
  never released. Whether the tag is right is public: `open` may leak it (it
  is the result), and nothing else secret.

The lengths are public, and the tag length and the nonce length, which the
algorithm depends on, are preconditions (`lengthsOk`: a tag of 1 to 16
bytes, a nonce of 1 to 15 bytes), which the caller checks; RFC 7253 bounds
no other length (§3.1). The tag travels in the first `tag_len` bytes of
`work`, which is also working space, so that fewer arguments are passed in
memory; each function's working space (`scratch` or `work`) has room for
`vg_aes_ctr32`'s (2048 bytes) and 512 bytes more.

Every contract takes the number of bytes of stack below the stack pointer
that an implementation's calls and frames use (`stack`, see `Sig.contract`),
0 for one that uses none; the functions may overwrite their arguments passed
in memory, where the calling convention allows it (`writeArgs`), to pass
arguments to the functions they call.
-/

namespace VG.Spec.Ocb

/-! ## The key context -/

/-- `vg_aes_ocb_init(key: *const u8, key_len: usize, ctx: *mut [u64; 32], scratch: *mut [u64; 320])`.
`scratch` is working space. -/
def initSig : Sig where
  params := [("key", .slice false .u8 "key_len"), ("ctx", .array true .u64 32),
    ("scratch", .array true .u64 320)]

/-- For a key of 16, 24 or 32 bytes at `key`, makes the 256 bytes at `ctx`
its key context: its key schedule and `L_* = ENCIPHER(K, zeros(128))`. -/
def initContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  initSig.contract A
    (pre := fun _key keyLen _ctx _scratch _ =>
      keyLen.toNat = 16 ∨ keyLen.toNat = 24 ∨ keyLen.toNat = 32)
    (post := fun key keyLen ctx _scratch m m' _ => KeyRepr m' ctx (Aes.bytesAt m key keyLen.toNat))
    (writeArgs := true)
    (stack := stack)

/-- `vg_aes_ocb_init` on every target. -/
def initApi : Api where
  module := "aes_ocb"
  name := "vg_aes_ocb_init"
  sig := initSig
  writeArgs := true
  contracts := some fun A stack => initContract A stack
  summary := "The AES-OCB key setup (RFC 7253 §4.1): writes the key context of the \
    `key_len`-byte AES key at `key` to `*ctx`: its key schedule for `Nr = key_len / 4 + 6` \
    rounds (FIPS 197 §5.2, as `vg_aes_expand_key` writes it) in the first `16 * (Nr + 1)` \
    bytes, and `L_* = ENCIPHER(K, zeros(128))` in bytes 240–255. The other bytes are \
    unspecified. The other `vg_aes_ocb_*` functions read it, with `Nr` as their `rounds`.\n\n\
    Contract: `VG.Spec.Ocb.initContract`. The key context is `VG.Spec.Ocb.KeyRepr`. Constant \
    time: only the pointers and `key_len` may affect timing, not the key."
  safety := [
    "`key_len` must be 16, 24 or 32.",
    "The contents of `scratch` on return are unspecified."]

/-! ## Encryption and decryption -/

/-- `vg_aes_ocb_seal(ctx: *const [u64; 32], rounds: usize, nonce: *const u8, nonce_len: usize, aad: *const u8, aad_len: usize, data: *mut u8, len: usize, work: *mut [u64; 320], tag_len: usize)`,
and `vg_aes_ocb_open` with the same parameters, returning a `u32`. `rounds`
and `tag_len` are public; `work` is working space but for the tag. -/
def sealSig : Sig where
  params := [("ctx", .array false .u64 32), ("rounds", .int .usize true),
    ("nonce", .slice false .u8 "nonce_len"), ("aad", .slice false .u8 "aad_len"),
    ("data", .slice true .u8 "len"), ("work", .array true .u64 320),
    ("tag_len", .int .usize true)]

/-- `vg_aes_ocb_open`'s signature: `vg_aes_ocb_seal`'s, returning a `u32`. -/
def openSig : Sig := { sealSig with ret := some .u32 }

/-- For `rounds` of 10, 12 or 14, a tag of 1 to 16 bytes and a nonce of 1 to
15 bytes, with the key context at `ctx`: encrypts the `len` bytes at `data`
in place, with the nonce at `nonce` and the `aad_len` bytes of associated
data at `aad` (`encryptWith`), and writes the tag of `tag_len` bytes to the
first `tag_len` bytes of `work`. -/
def sealContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  sealSig.contract A
    (pre := fun _ctx rounds _nonce nonceLen _aad _aadLen _data _len _work tagLen _ =>
      (rounds.toNat = 10 ∨ rounds.toNat = 12 ∨ rounds.toNat = 14) ∧
        lengthsOk tagLen.toNat nonceLen.toNat)
    (post := fun ctx rounds nonce nonceLen aad aadLen data len work tagLen m m' _ =>
      encryptWith (ctxCiph m ctx rounds.toNat) (ctxLstar m ctx) tagLen.toNat
          (Aes.bytesAt m nonce nonceLen.toNat) (Aes.bytesAt m aad aadLen.toNat)
          (Aes.bytesAt m data len.toNat) =
        (Aes.bytesAt m' data len.toNat, Aes.bytesAt m' work tagLen.toNat))
    (writeArgs := true)
    (stack := stack)

/-- `vg_aes_ocb_seal` on every target. -/
def sealApi : Api where
  module := "aes_ocb"
  name := "vg_aes_ocb_seal"
  sig := sealSig
  writeArgs := true
  contracts := some fun A stack => sealContract A stack
  summary := "AES-OCB authenticated encryption (RFC 7253 §4.2, `OCB-ENCRYPT`, with \
    `TAGLEN = 8 * tag_len`): with the key context `*ctx` that `vg_aes_ocb_init` wrote for \
    `rounds` rounds, encrypts the `len` bytes at `data` in place, under the `nonce_len`-byte \
    nonce at `nonce`, and writes the tag of `tag_len` bytes, of the data and the `aad_len` \
    bytes of associated data at `aad`, to the first `tag_len` bytes of `*work`. The RFC's \
    ciphertext is the encrypted data followed by the tag. The rest of `*work` is working \
    space, unspecified on return. A nonce must never be used twice with the same key.\n\n\
    Contract: `VG.Spec.Ocb.sealContract`. Constant time: only the pointers, `rounds`, the \
    lengths and `tag_len` may affect timing, not the key context, the nonce, the associated \
    data or the data."
  safety := [
    "`rounds` must be 10, 12 or 14.",
    "`tag_len` must be from 1 to 16, and `nonce_len` from 1 to 15 (RFC 7253 §3.1)."]

/-- For `rounds` of 10, 12 or 14, a tag of 1 to 16 bytes and a nonce of 1 to
15 bytes, with the key context at `ctx` and the received tag in the first
`tag_len` bytes of `work`: if the tag is right for the `len` bytes of
encrypted data at `data`, the nonce at `nonce` and the `aad_len` bytes of
associated data at `aad` (`decryptWith`), returns 1 and leaves the plaintext
at `data`; otherwise returns 0 and leaves zeros at `data`. May leak which
(`decryptWith`'s outcome). -/
def openContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  openSig.contract A
    (pre := fun _ctx rounds _nonce nonceLen _aad _aadLen _data _len _work tagLen _ =>
      (rounds.toNat = 10 ∨ rounds.toNat = 12 ∨ rounds.toNat = 14) ∧
        lengthsOk tagLen.toNat nonceLen.toNat)
    (post := fun ctx rounds nonce nonceLen aad aadLen data len work tagLen m m' r =>
      match decryptWith (ctxCiph m ctx rounds.toNat) (ctxInv m ctx rounds.toNat)
          (ctxLstar m ctx) tagLen.toNat (Aes.bytesAt m nonce nonceLen.toNat)
          (Aes.bytesAt m aad aadLen.toNat) (Aes.bytesAt m data len.toNat)
          (Aes.bytesAt m work tagLen.toNat) with
      | some pt => r = 1 ∧ Aes.bytesAt m' data len.toNat = pt
      | none => r = 0 ∧ Aes.bytesAt m' data len.toNat = zeros len.toNat)
    (writeArgs := true)
    (stack := stack)
    (leak := some fun ctx rounds nonce nonceLen aad aadLen data len work tagLen m =>
      [if (decryptWith (ctxCiph m ctx rounds.toNat) (ctxInv m ctx rounds.toNat)
          (ctxLstar m ctx) tagLen.toNat (Aes.bytesAt m nonce nonceLen.toNat)
          (Aes.bytesAt m aad aadLen.toNat) (Aes.bytesAt m data len.toNat)
          (Aes.bytesAt m work tagLen.toNat)).isSome
        then 1 else 0])

/-- `vg_aes_ocb_open` on every target. -/
def openApi : Api where
  module := "aes_ocb"
  name := "vg_aes_ocb_open"
  sig := openSig
  writeArgs := true
  contracts := some fun A stack => openContract A stack
  summary := "AES-OCB authenticated decryption (RFC 7253 §4.3, `OCB-DECRYPT`, with \
    `TAGLEN = 8 * tag_len`): with the key context `*ctx` that `vg_aes_ocb_init` wrote for \
    `rounds` rounds and the received tag (the last `tag_len` bytes of the RFC's ciphertext) in \
    the first `tag_len` bytes of `*work`, decrypts the `len` bytes of encrypted data at `data` \
    in place, under the `nonce_len`-byte nonce at `nonce`, and returns 1 if the tag is that of \
    the data and the `aad_len` bytes of associated data at `aad`; otherwise returns 0 and \
    overwrites the `len` bytes at `data` with zeros. The rest of `*work` is working space, \
    unspecified on return. The tags are compared without a branch.\n\n\
    Contract: `VG.Spec.Ocb.openContract`. Constant time but for the result: only the pointers, \
    `rounds`, the lengths, `tag_len` and whether the function returns 1 or 0 may affect timing, \
    not the key context, the nonce, the associated data, the data or the tag."
  safety := [
    "`rounds` must be 10, 12 or 14.",
    "`tag_len` must be from 1 to 16, and `nonce_len` from 1 to 15 (RFC 7253 §3.1)."]

end VG.Spec.Ocb
