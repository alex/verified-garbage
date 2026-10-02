import VerifiedGarbage.Spec.Gcm
import VerifiedGarbage.TCB.Artifact

/-!
# AES-GCM: the contracts, on every target

**Trusted** (as every file in `Spec/`). The contracts of the primitives
AES-GCM is built from, and of AES-GCM itself, in terms of `Spec/Gcm.lean`,
for any target: `A` is the target's calling convention. The signatures fix
where the arguments are, the memory each function may access, disjointness,
and that the pointers, the lengths and the number of rounds are public (see
`TCB/Sig.lean`); the contracts add the rest. Everything else (keys, key
schedules, hash subkeys, IVs, additional data, texts, tags and states) is
secret.

## The primitives

* `vg_aes_ctr32` XORs AES counter-mode keystream (with GCM's `inc₃₂`) into
  whole blocks in place, from a key schedule that `vg_aes_expand_key`
  (`VG.Spec.Aes.expandKeyContract`) wrote. With a zero block it computes
  `H = CIPH_K(0¹²⁸)`, and with `S` it computes the unmasked tag
  `S ⊕ CIPH_K(J₀)`.
* `vg_ghash` continues `GHASH_H` over whole blocks.

Each takes a `scratch` buffer of working space, sized for the target that
needs the most.

## AES-GCM

The functions of AES-GCM do all of GCM-AE and GCM-AD (§7) but check no
lengths (which are public): the caller checks the key length and the number of
rounds (the preconditions), and the lengths of §5.2.1.1 (`supported`), which
GCM needs to be secure but which concern a whole message, which a streaming
caller gives in pieces. Only the length of a received tag is checked by the
function given the tag, which rejects a length §5.2.1.2 does not allow
(`tagLenOk`) as it rejects a wrong tag: a tag of 0 bytes would accept any
message.

* `vg_aes_gcm_init` writes a key context (`KeyRepr`): the key schedule and
  the hash subkey `H`. The others read one (with its number of rounds, if
  they need the cipher), and compute with the cipher and the hash subkey it
  holds (`ctxCiph`, `ctxH`): with a context `vg_aes_gcm_init` wrote, that
  is AES-GCM with its key (`encryptWith_ctx`, `decryptWith_ctx`).
* `vg_aes_gcm_seal` is GCM-AE (`encryptWith`) with a 16-byte tag, and
  `vg_aes_gcm_open` GCM-AD (`decryptWith`) with a tag of any length
  §5.2.1.2 allows; `open` decrypts only if the tag is right, and otherwise
  leaves the data as it was. Whether the tag is right is public: `open` may
  leak it (it is the result), and nothing else secret.
* The streaming functions, on a state that `vg_aes_gcm_stream_init` starts
  (`StreamRepr`): `vg_aes_gcm_stream_aad` absorbs additional data,
  `vg_aes_gcm_stream_encrypt` and `vg_aes_gcm_stream_decrypt` encrypt or
  decrypt text in place, `vg_aes_gcm_stream_finish` writes the 16-byte tag,
  and `vg_aes_gcm_stream_verify` compares it with a received tag. The
  caller keeps the lengths of the additional data and the text so far,
  which are public (as the hashes' callers keep `count`), and passes them.

The data, the additional data and the IV are in buffers of their own; the
data is encrypted or decrypted in place. The fixed-size secrets travel in
buffers that are also working space, so that fewer arguments are passed in
memory: the tags in the first 16 bytes of `work`. Each function's working
space (`scratch` or `work`) has room for `vg_aes_ctr32`'s (2048 bytes) and
512 bytes more.

Every contract takes the number of bytes of stack below the stack pointer
that an implementation's calls and frames use (`stack`, see `Sig.contract`),
0 for one that uses none; the functions of AES-GCM may overwrite their
arguments passed in memory, where the calling convention allows it
(`writeArgs`), to pass arguments to the functions they call.
-/

namespace VG.Spec.Gcm

/-- `vg_aes_ctr32(schedule: *const [u8; 240], rounds: usize, counter: *mut [u8; 16], data: *mut [u8; 16], n: usize, scratch: *mut [u64; 256])`.
`rounds` is public; `scratch` is working space. -/
def ctr32Sig : Sig where
  params := [("schedule", .array false .u8 240), ("rounds", .int .usize true),
    ("counter", .array true .u8 16), ("data", .slice true (.array .u8 16) "n"),
    ("scratch", .array true .u64 256)]

/-- For `rounds` of 10, 12 or 14, with the key schedule `w` in the first
`16 (rounds + 1)` bytes at `schedule`: XORs `CIPH_K(CB₁) … CIPH_K(CBₙ)`
into the `n` blocks at `data`, where `CB₁` is the block at `counter` and
`CBᵢ₊₁ = inc₃₂(CBᵢ)`, and leaves `inc₃₂ⁿ(CB₁)` at `counter`. The key
schedule, the counter and the data are secret. -/
def ctr32Contract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  ctr32Sig.contract A
    (pre := fun _schedule rounds _counter _data _n _scratch _ =>
      rounds.toNat = 10 ∨ rounds.toNat = 12 ∨ rounds.toNat = 14)
    (post := fun schedule rounds counter data n _scratch m m' _ =>
      let ciph := aesWith rounds.toNat (Aes.bytesAt m schedule (16 * (rounds.toNat + 1)))
      blocksAt m' data n.toNat = ctr32 ciph (blockAt m counter) (blocksAt m data n.toNat) ∧
        blockAt m' counter = Nat.repeat inc32 n.toNat (blockAt m counter))
    (stack := stack)

/-- `vg_aes_ctr32` on every target. -/
def ctr32Api : Api where
  module := "aes"
  name := "vg_aes_ctr32"
  sig := ctr32Sig
  contracts := some fun A stack => ctr32Contract A stack
  summary := "AES counter mode with GCM's 32-bit increment (NIST SP 800-38D §6.5, on whole \
    blocks): XORs `CIPH_K(CB₁) … CIPH_K(CBₙ)` into the `n` 16-byte blocks at `data`, where `CB₁` \
    is the counter block `*counter` and `CBᵢ₊₁ = inc₃₂(CBᵢ)`, and leaves `inc₃₂ⁿ(CB₁)` in \
    `*counter`. `CIPH_K` is AES (FIPS 197) with `rounds` rounds and the key schedule in the first \
    `16 * (rounds + 1)` bytes of `*schedule`, as `vg_aes_expand_key` writes it.\n\n\
    Contract: `VG.Spec.Gcm.ctr32Contract`. Constant time: only the pointers, `rounds` and `n` may \
    affect timing, not the key schedule, the counter block or the data."
  safety := [
    "`rounds` must be 10, 12 or 14.",
    "The contents of `scratch` on return are unspecified."]

/-- `vg_ghash(h: *const [u8; 16], y: *mut [u8; 16], data: *const [u8; 16], n: usize, scratch: *mut [u64; 32])`.
`scratch` is working space. -/
def ghashSig : Sig where
  params := [("h", .array false .u8 16), ("y", .array true .u8 16),
    ("data", .slice false (.array .u8 16) "n"), ("scratch", .array true .u64 32)]

/-- With the hash subkey `H` at `h` and a block `Y` at `y`: replaces `Y`
with `GHASH_H` continued from `Y` over the `n` blocks at `data`
(`Yᵢ = (Yᵢ₋₁ ⊕ Xᵢ) • H`). The hash subkey, `Y` and the data are secret. -/
def ghashContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  ghashSig.contract A (post := fun h y data n _scratch m m' _ =>
    blockAt m' y = ghashFrom (blockAt m h) (blockAt m y) (blocksAt m data n.toNat))
    (stack := stack)

/-- `vg_ghash` on every target. -/
def ghashApi : Api where
  module := "gcm"
  name := "vg_ghash"
  sig := ghashSig
  contracts := some fun A stack => ghashContract A stack
  summary := "GHASH (NIST SP 800-38D §6.4) continued over whole blocks: with the hash subkey `H` \
    the block at `h`, replaces the block `Y` at `*y` with `Yₙ`, where `Y₀ = Y` and \
    `Yᵢ = (Yᵢ₋₁ ⊕ Xᵢ) • H` for the `n` 16-byte blocks `X₁ … Xₙ` starting at `data` (blocks \
    big-endian, `•` the multiplication of §6.3).\n\n\
    Contract: `VG.Spec.Gcm.ghashContract`. Constant time: only the pointers and `n` may affect \
    timing, not `H`, `Y` or the data."
  safety := ["The contents of `scratch` on return are unspecified."]

/-! ## AES-GCM: the key context -/

/-- `vg_aes_gcm_init(key: *const u8, key_len: usize, ctx: *mut [u64; 32], scratch: *mut [u64; 320])`.
`scratch` is working space. -/
def initSig : Sig where
  params := [("key", .slice false .u8 "key_len"), ("ctx", .array true .u64 32),
    ("scratch", .array true .u64 320)]

/-- For a key of 16, 24 or 32 bytes at `key`, makes the 256 bytes at `ctx`
its key context: its key schedule and its hash subkey `CIPH_K(0¹²⁸)`. -/
def initContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  initSig.contract A
    (pre := fun _key keyLen _ctx _scratch _ =>
      keyLen.toNat = 16 ∨ keyLen.toNat = 24 ∨ keyLen.toNat = 32)
    (post := fun key keyLen ctx _scratch m m' _ => KeyRepr m' ctx (Aes.bytesAt m key keyLen.toNat))
    (writeArgs := true)
    (stack := stack)

/-- `vg_aes_gcm_init` on every target. -/
def initApi : Api where
  module := "gcm"
  name := "vg_aes_gcm_init"
  sig := initSig
  writeArgs := true
  contracts := some fun A stack => initContract A stack
  summary := "The AES-GCM key setup: writes the key context of the `key_len`-byte AES key at \
    `key` to `*ctx`: its key schedule for `Nr = key_len / 4 + 6` rounds (FIPS 197 §5.2, as \
    `vg_aes_expand_key` writes it) in the first `16 * (Nr + 1)` bytes, and the hash subkey \
    `H = CIPH_K(0¹²⁸)` (NIST SP 800-38D §7.1 step 1) in bytes 240–255. The other bytes are \
    unspecified. The other `vg_aes_gcm_*` functions read it, with `Nr` as their `rounds`.\n\n\
    Contract: `VG.Spec.Gcm.initContract`. The key context is `VG.Spec.Gcm.KeyRepr`. Constant \
    time: only the pointers and `key_len` may affect timing, not the key."
  safety := [
    "`key_len` must be 16, 24 or 32.",
    "The contents of `scratch` on return are unspecified."]

/-! ## AES-GCM: one-shot -/

/-- `vg_aes_gcm_seal(ctx: *const [u64; 32], rounds: usize, nonce: *const u8, nonce_len: usize, aad: *const u8, aad_len: usize, data: *mut u8, len: usize, work: *mut [u64; 320])`.
`rounds` is public; `work` is working space but for the tag it returns. -/
def sealSig : Sig where
  params := [("ctx", .array false .u64 32), ("rounds", .int .usize true),
    ("nonce", .slice false .u8 "nonce_len"), ("aad", .slice false .u8 "aad_len"),
    ("data", .slice true .u8 "len"), ("work", .array true .u64 320)]

/-- For `rounds` of 10, 12 or 14, with the key context at `ctx`: encrypts the
`len` bytes at `data` in place, with the IV the `nonce_len` bytes at `nonce`
and the `aad_len` bytes of additional data at `aad` (GCM-AE, `encryptWith`),
and writes the 16-byte tag to the first 16 bytes of `work`. -/
def sealContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  sealSig.contract A
    (pre := fun _ctx rounds _nonce _nonceLen _aad _aadLen _data _len _work _ =>
      rounds.toNat = 10 ∨ rounds.toNat = 12 ∨ rounds.toNat = 14)
    (post := fun ctx rounds nonce nonceLen aad aadLen data len work m m' _ =>
      encryptWith (ctxCiph m ctx rounds.toNat) (ctxH m ctx) 16 (Aes.bytesAt m nonce nonceLen.toNat)
          (Aes.bytesAt m data len.toNat) (Aes.bytesAt m aad aadLen.toNat) =
        (Aes.bytesAt m' data len.toNat, Aes.bytesAt m' work 16))
    (writeArgs := true)
    (stack := stack)

/-- `vg_aes_gcm_seal` on every target. -/
def sealApi : Api where
  module := "gcm"
  name := "vg_aes_gcm_seal"
  sig := sealSig
  writeArgs := true
  contracts := some fun A stack => sealContract A stack
  summary := "AES-GCM authenticated encryption (NIST SP 800-38D §7.1, GCM-AE, with a 128-bit \
    tag): with the key context `*ctx` that `vg_aes_gcm_init` wrote for `rounds` rounds, \
    encrypts the `len` bytes at `data` in place, under the IV the `nonce_len` bytes at `nonce`, \
    and writes the tag of the ciphertext and the `aad_len` bytes of additional data at `aad` \
    to the first 16 bytes of `*work`. The rest of `*work` is working space, unspecified on \
    return. A shorter tag is the first bytes of this one.\n\n\
    The function checks no length. GCM is secure only for a nonce of 1 to `2^61 - 1` bytes, \
    at most `2^36 - 32` bytes of data and at most `2^61 - 1` bytes of additional data \
    (§5.2.1.1), which the caller must ensure; and a nonce must never be used twice with the \
    same key.\n\n\
    Contract: `VG.Spec.Gcm.sealContract`. Constant time: only the pointers, `rounds` and the \
    lengths may affect timing, not the key context, the nonce, the additional data or the \
    data."
  safety := ["`rounds` must be 10, 12 or 14."]

/-- `vg_aes_gcm_open(ctx: *const [u64; 32], rounds: usize, nonce: *const u8, nonce_len: usize, aad: *const u8, aad_len: usize, data: *mut u8, len: usize, work: *mut [u64; 320], tag_len: usize) -> u32`.
`rounds` and `tag_len` are public; `work` is working space but for the tag
it is given. -/
def openSig : Sig where
  params := [("ctx", .array false .u64 32), ("rounds", .int .usize true),
    ("nonce", .slice false .u8 "nonce_len"), ("aad", .slice false .u8 "aad_len"),
    ("data", .slice true .u8 "len"), ("work", .array true .u64 320),
    ("tag_len", .int .usize true)]
  ret := some .u32

/-- What `vg_aes_gcm_open` computes: GCM-AD (`decryptWith`) for a tag of
`tagLen` bytes, if §5.2.1.2 allows that length, and `none` (FAIL) if not. -/
def openResult (ciph : Block → Block) (h : Block) (tagLen : Nat) (iv c a tag : List Byte) :
    Option (List Byte) :=
  if tagLenOk tagLen then decryptWith ciph h tagLen iv c a tag else none

/-- For `rounds` of 10, 12 or 14, with the key context at `ctx` and the
received tag in the first `tag_len` bytes of `work`: if `tag_len` is a tag
length §5.2.1.2 allows and the tag is that of the `len` bytes of ciphertext
at `data` and the `aad_len` bytes of additional data at `aad`, with the IV
the `nonce_len` bytes at `nonce` (GCM-AD, `decryptWith`), returns 1 and
leaves the plaintext at `data`; otherwise returns 0 and leaves the bytes at
`data` as they were. May leak which (`openResult`'s outcome). -/
def openContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  openSig.contract A
    (pre := fun _ctx rounds _nonce _nonceLen _aad _aadLen _data _len _work _tagLen _ =>
      rounds.toNat = 10 ∨ rounds.toNat = 12 ∨ rounds.toNat = 14)
    (post := fun ctx rounds nonce nonceLen aad aadLen data len work tagLen m m' r =>
      match openResult (ctxCiph m ctx rounds.toNat) (ctxH m ctx) tagLen.toNat
          (Aes.bytesAt m nonce nonceLen.toNat) (Aes.bytesAt m data len.toNat)
          (Aes.bytesAt m aad aadLen.toNat) (Aes.bytesAt m work tagLen.toNat) with
      | some pt => r = 1 ∧ Aes.bytesAt m' data len.toNat = pt
      | none => r = 0 ∧ Aes.bytesAt m' data len.toNat = Aes.bytesAt m data len.toNat)
    (writeArgs := true)
    (stack := stack)
    (leak := some fun ctx rounds nonce nonceLen aad aadLen data len work tagLen m =>
      [if (openResult (ctxCiph m ctx rounds.toNat) (ctxH m ctx) tagLen.toNat
          (Aes.bytesAt m nonce nonceLen.toNat) (Aes.bytesAt m data len.toNat)
          (Aes.bytesAt m aad aadLen.toNat) (Aes.bytesAt m work tagLen.toNat)).isSome
        then 1 else 0])

/-- `vg_aes_gcm_open` on every target. -/
def openApi : Api where
  module := "gcm"
  name := "vg_aes_gcm_open"
  sig := openSig
  writeArgs := true
  contracts := some fun A stack => openContract A stack
  summary := "AES-GCM authenticated decryption (NIST SP 800-38D §7.2, GCM-AD): with the key \
    context `*ctx` that `vg_aes_gcm_init` wrote for `rounds` rounds and the received tag in \
    the first `tag_len` bytes of `*work`, returns 1 if `tag_len` is 4, 8, 12, 13, 14, 15 or 16 \
    (§5.2.1.2) and the tag is the first `tag_len` bytes of that of the `len` bytes of \
    ciphertext at `data` and the `aad_len` bytes of additional data at `aad`, under the IV the \
    `nonce_len` bytes at `nonce`, having then decrypted the ciphertext in place; otherwise \
    returns 0, and the bytes at `data` are unchanged. The rest of `*work` is working space, \
    unspecified on return. The tags are compared without a branch.\n\n\
    The function checks no other length: GCM requires a nonce of 1 to `2^61 - 1` bytes, at \
    most `2^36 - 32` bytes of ciphertext and at most `2^61 - 1` bytes of additional data \
    (§5.2.1.1), which the caller must check.\n\n\
    Contract: `VG.Spec.Gcm.openContract`. Constant time but for the result: only the pointers, \
    `rounds`, the lengths, `tag_len` and whether the function returns 1 or 0 may affect \
    timing, not the key context, the nonce, the additional data, the data or the tag."
  safety := ["`rounds` must be 10, 12 or 14."]

/-! ## AES-GCM: streaming -/

/-- `vg_aes_gcm_stream_init(ctx: *const [u64; 32], nonce: *const u8, nonce_len: usize, state: *mut [u64; 10], scratch: *mut [u64; 320])`.
`scratch` is working space. -/
def streamInitSig : Sig where
  params := [("ctx", .array false .u64 32), ("nonce", .slice false .u8 "nonce_len"),
    ("state", .array true .u64 10), ("scratch", .array true .u64 320)]

/-- With the key context at `ctx`: makes the streaming state at `state`
represent the message with the IV the `nonce_len` bytes at `nonce`, no
additional data and no text yet, for any cipher (which only the text
needs). -/
def streamInitContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  streamInitSig.contract A
    (post := fun ctx nonce nonceLen state _scratch m m' _ =>
      ∀ ciph, StreamRepr m' state ciph (ctxH m ctx) (Aes.bytesAt m nonce nonceLen.toNat) [] [])
    (writeArgs := true)
    (stack := stack)

/-- `vg_aes_gcm_stream_init` on every target. -/
def streamInitApi : Api where
  module := "gcm"
  name := "vg_aes_gcm_stream_init"
  sig := streamInitSig
  writeArgs := true
  contracts := some fun A stack => streamInitContract A stack
  summary := "Starts an incremental AES-GCM encryption or decryption (NIST SP 800-38D §7): with \
    the key context `*ctx` that `vg_aes_gcm_init` wrote, makes the streaming state `*state` \
    represent the message with the IV the `nonce_len` bytes at `nonce`, and no additional \
    data or text yet. Continue with `vg_aes_gcm_stream_aad`, then `vg_aes_gcm_stream_encrypt` \
    or `vg_aes_gcm_stream_decrypt`, then `vg_aes_gcm_stream_finish` or \
    `vg_aes_gcm_stream_verify`, with the same key context.\n\n\
    The function checks no length: GCM requires a nonce of 1 to `2^61 - 1` bytes (§5.2.1.1), \
    which the caller must check.\n\n\
    Contract: `VG.Spec.Gcm.streamInitContract`. The streaming state is `J₀`, the GHASH \
    accumulator, a partial block, the next counter block and a keystream block \
    (`VG.Spec.Gcm.StreamRepr`). Constant time: only the pointers and `nonce_len` may affect \
    timing, not the key context or the nonce."
  safety := ["The contents of `scratch` on return are unspecified."]

/-- `vg_aes_gcm_stream_aad(ctx: *const [u64; 32], state: *mut [u64; 10], aad_len: u64, data: *const u8, len: usize, scratch: *mut [u64; 320])`.
`aad_len` is public; `scratch` is working space. -/
def streamAadSig : Sig where
  params := [("ctx", .array false .u64 32), ("state", .array true .u64 10),
    ("aad_len", .int .u64 true), ("data", .slice false .u8 "len"),
    ("scratch", .array true .u64 320)]

/-- With the key context at `ctx`: if the streaming state at `state`
represents a message with additional data `a` of `aad_len` bytes (modulo
2⁶⁴) and no text yet, for its hash subkey, then afterwards it represents
that message with `a` followed by the `len` bytes at `data` as its
additional data. -/
def streamAadContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  streamAadSig.contract A
    (post := fun ctx state aadLen data len _scratch m m' _ =>
      ∀ ciph iv a, StreamRepr m state ciph (ctxH m ctx) iv a [] →
        aadLen = BitVec.ofNat 64 a.length →
        StreamRepr m' state ciph (ctxH m ctx) iv (a ++ Aes.bytesAt m data len.toNat) [])
    (writeArgs := true)
    (stack := stack)

/-- `vg_aes_gcm_stream_aad` on every target. -/
def streamAadApi : Api where
  module := "gcm"
  name := "vg_aes_gcm_stream_aad"
  sig := streamAadSig
  writeArgs := true
  contracts := some fun A stack => streamAadContract A stack
  summary := "Absorbs additional data into an incremental AES-GCM encryption or decryption: with \
    the key context `*ctx`, if the streaming state `*state` represents a message with \
    `aad_len` bytes (modulo 2⁶⁴) of additional data and no text yet, it then represents that \
    message with the `len` bytes at `data` appended to its additional data. All of the \
    additional data comes before the text (§7.1 step 5): after text, the state represents no \
    message.\n\n\
    Contract: `VG.Spec.Gcm.streamAadContract`. Constant time: only the pointers, `aad_len` and \
    `len` may affect timing, not the key context, the state or the data."
  safety := ["The contents of `scratch` on return are unspecified."]

/-- `vg_aes_gcm_stream_encrypt(ctx: *const [u64; 32], rounds: usize, state: *mut [u64; 10], aad_len: u64, text_len: u64, data: *mut u8, len: usize, scratch: *mut [u64; 320])`,
and `vg_aes_gcm_stream_decrypt` with the same signature. `rounds`, `aad_len`
and `text_len` are public; `scratch` is working space. -/
def streamCryptSig : Sig where
  params := [("ctx", .array false .u64 32), ("rounds", .int .usize true),
    ("state", .array true .u64 10), ("aad_len", .int .u64 true), ("text_len", .int .u64 true),
    ("data", .slice true .u8 "len"), ("scratch", .array true .u64 320)]

/-- For `rounds` of 10, 12 or 14, with the key context at `ctx`: if the
streaming state at `state` represents a message with the IV `iv`,
additional data `a` of `aad_len` bytes and the ciphertext of a plaintext
`p` of exactly `text_len` bytes (and `aad_len` modulo 2⁶⁴) so far, then afterwards it
represents the message with the ciphertext of `p` followed by the `len`
bytes at `data`, whose encryption is written to `data`: the last `len`
bytes of `GCTR_K(inc₃₂(J₀), p ‖ data)`. -/
def streamEncryptContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  streamCryptSig.contract A
    (pre := fun _ctx rounds _state _aadLen _textLen _data _len _scratch _ =>
      rounds.toNat = 10 ∨ rounds.toNat = 12 ∨ rounds.toNat = 14)
    (post := fun ctx rounds state aadLen textLen data len _scratch m m' _ =>
      let ciph := ctxCiph m ctx rounds.toNat
      let h := ctxH m ctx
      ∀ iv a p, StreamRepr m state ciph h iv a (gctr ciph (inc32 (j0 h iv)) p) →
        aadLen = BitVec.ofNat 64 a.length → textLen.toNat = p.length →
        let c := gctr ciph (inc32 (j0 h iv)) (p ++ Aes.bytesAt m data len.toNat)
        StreamRepr m' state ciph h iv a c ∧ Aes.bytesAt m' data len.toNat = c.drop p.length)
    (writeArgs := true)
    (stack := stack)

/-- `vg_aes_gcm_stream_encrypt` on every target. -/
def streamEncryptApi : Api where
  module := "gcm"
  name := "vg_aes_gcm_stream_encrypt"
  sig := streamCryptSig
  writeArgs := true
  contracts := some fun A stack => streamEncryptContract A stack
  summary := "Encrypts the next piece of the text of an incremental AES-GCM encryption (NIST SP \
    800-38D §7.1): with the key context `*ctx` that `vg_aes_gcm_init` wrote for `rounds` \
    rounds, if the streaming state `*state` represents a message with `aad_len` bytes of \
    additional data and the ciphertext of exactly `text_len` bytes of plaintext so far, \
    encrypts the `len` bytes at `data` in place, as the continuation of that plaintext, and \
    the state then represents the message with them appended.\n\n\
    The function checks no length: GCM requires at most `2^36 - 32` bytes of text and at most \
    `2^61 - 1` bytes of additional data (§5.2.1.1), which the caller must check.\n\n\
    Contract: `VG.Spec.Gcm.streamEncryptContract`. Constant time: only the pointers, `rounds`, \
    `aad_len`, `text_len` and `len` may affect timing, not the key context, the state or the \
    data."
  safety := [
    "`rounds` must be 10, 12 or 14.",
    "The contents of `scratch` on return are unspecified."]

/-- For `rounds` of 10, 12 or 14, with the key context at `ctx`: if the
streaming state at `state` represents a message with the IV `iv`,
additional data `a` of `aad_len` bytes and the ciphertext `c` of `text_len`
bytes (exactly, and `aad_len` modulo 2⁶⁴) so far, then afterwards it represents the message
with the ciphertext `c` followed by the `len` bytes at `data`, whose
decryption is written to `data`: the last `len` bytes of
`GCTR_K(inc₃₂(J₀), c ‖ data)`. -/
def streamDecryptContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  streamCryptSig.contract A
    (pre := fun _ctx rounds _state _aadLen _textLen _data _len _scratch _ =>
      rounds.toNat = 10 ∨ rounds.toNat = 12 ∨ rounds.toNat = 14)
    (post := fun ctx rounds state aadLen textLen data len _scratch m m' _ =>
      let ciph := ctxCiph m ctx rounds.toNat
      let h := ctxH m ctx
      ∀ iv a c, StreamRepr m state ciph h iv a c →
        aadLen = BitVec.ofNat 64 a.length → textLen.toNat = c.length →
        let c' := c ++ Aes.bytesAt m data len.toNat
        StreamRepr m' state ciph h iv a c' ∧
          Aes.bytesAt m' data len.toNat = (gctr ciph (inc32 (j0 h iv)) c').drop c.length)
    (writeArgs := true)
    (stack := stack)

/-- `vg_aes_gcm_stream_decrypt` on every target. -/
def streamDecryptApi : Api where
  module := "gcm"
  name := "vg_aes_gcm_stream_decrypt"
  sig := streamCryptSig
  writeArgs := true
  contracts := some fun A stack => streamDecryptContract A stack
  summary := "Decrypts the next piece of the text of an incremental AES-GCM decryption (NIST SP \
    800-38D §7.2): with the key context `*ctx` that `vg_aes_gcm_init` wrote for `rounds` \
    rounds, if the streaming state `*state` represents a message with `aad_len` bytes of \
    additional data and exactly `text_len` bytes of ciphertext so far, decrypts the `len` \
    bytes of ciphertext at `data` in place, as the continuation of that ciphertext, and the \
    state then represents the message with them appended. The plaintext is not authenticated \
    until `vg_aes_gcm_stream_verify` has returned 1.\n\n\
    The function checks no length: GCM requires at most `2^36 - 32` bytes of text and at most \
    `2^61 - 1` bytes of additional data (§5.2.1.1), which the caller must check.\n\n\
    Contract: `VG.Spec.Gcm.streamDecryptContract`. Constant time: only the pointers, `rounds`, \
    `aad_len`, `text_len` and `len` may affect timing, not the key context, the state or the \
    data."
  safety := [
    "`rounds` must be 10, 12 or 14.",
    "The contents of `scratch` on return are unspecified."]

/-- `vg_aes_gcm_stream_finish(ctx: *const [u64; 32], rounds: usize, state: *mut [u64; 10], aad_len: u64, text_len: u64, work: *mut [u64; 320])`.
`rounds`, `aad_len` and `text_len` are public; `state` is left unspecified,
and `work` is working space but for the tag it returns. -/
def streamFinishSig : Sig where
  params := [("ctx", .array false .u64 32), ("rounds", .int .usize true),
    ("state", .array true .u64 10), ("aad_len", .int .u64 true), ("text_len", .int .u64 true),
    ("work", .array true .u64 320)]

/-- For `rounds` of 10, 12 or 14, with the key context at `ctx`: if the
streaming state at `state` represents a message with the IV `iv`,
additional data `a` of `aad_len` bytes and the ciphertext `c` of `text_len`
bytes (exactly, and `aad_len` modulo 2⁶⁴), writes its 16-byte tag (`fullTag`) to the first 16
bytes of `work`. -/
def streamFinishContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  streamFinishSig.contract A
    (pre := fun _ctx rounds _state _aadLen _textLen _work _ =>
      rounds.toNat = 10 ∨ rounds.toNat = 12 ∨ rounds.toNat = 14)
    (post := fun ctx rounds state aadLen textLen work m m' _ =>
      let ciph := ctxCiph m ctx rounds.toNat
      let h := ctxH m ctx
      ∀ iv a c, StreamRepr m state ciph h iv a c →
        aadLen = BitVec.ofNat 64 a.length → textLen.toNat = c.length →
        Aes.bytesAt m' work 16 = fullTag ciph h iv a c)
    (writeArgs := true)
    (stack := stack)

/-- `vg_aes_gcm_stream_finish` on every target. -/
def streamFinishApi : Api where
  module := "gcm"
  name := "vg_aes_gcm_stream_finish"
  sig := streamFinishSig
  writeArgs := true
  contracts := some fun A stack => streamFinishContract A stack
  summary := "Finishes an incremental AES-GCM encryption or decryption (NIST SP 800-38D §7.1 \
    steps 5–6, §7.2 steps 6–7): with the key context `*ctx` that `vg_aes_gcm_init` wrote for \
    `rounds` rounds, if the streaming state `*state` represents a message with `aad_len` bytes \
    of additional data and exactly `text_len` bytes of ciphertext, writes its 128-bit \
    tag to the first 16 bytes of `*work`. The rest of `*work` is working space, unspecified \
    on return. A shorter tag is the first bytes of this one; to check a received tag, use \
    `vg_aes_gcm_stream_verify`.\n\n\
    Contract: `VG.Spec.Gcm.streamFinishContract`. Constant time: only the pointers, `rounds`, \
    `aad_len` and `text_len` may affect timing, not the key context or the state."
  safety := [
    "`rounds` must be 10, 12 or 14.",
    "The contents of `state` on return are unspecified."]

/-- `vg_aes_gcm_stream_verify(ctx: *const [u64; 32], rounds: usize, state: *mut [u64; 10], aad_len: u64, text_len: u64, work: *mut [u64; 320], tag_len: usize) -> u32`.
`rounds`, `aad_len`, `text_len` and `tag_len` are public; `state` is left
unspecified, and `work` is working space but for the tags. -/
def streamVerifySig : Sig where
  params := [("ctx", .array false .u64 32), ("rounds", .int .usize true),
    ("state", .array true .u64 10), ("aad_len", .int .u64 true), ("text_len", .int .u64 true),
    ("work", .array true .u64 320), ("tag_len", .int .usize true)]
  ret := some .u32

/-- For `rounds` of 10, 12 or 14, with the key context at `ctx` and the
received tag in the first `tag_len` bytes of `work`: if the streaming state
at `state` represents a message with the IV `iv`, additional data `a` of
`aad_len` bytes and the ciphertext `c` of `text_len` bytes (both modulo
2⁶⁴), and `T` is its 16-byte tag (`fullTag`): if `tag_len` is a length
§5.2.1.2 allows and the received tag is the first `tag_len` bytes of `T`
(§7.2 step 8), returns 1 and writes `T` to the first 16 bytes of `work`;
otherwise returns 0 and writes 16 zero bytes there. -/
def streamVerifyContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  streamVerifySig.contract A
    (pre := fun _ctx rounds _state _aadLen _textLen _work _tagLen _ =>
      rounds.toNat = 10 ∨ rounds.toNat = 12 ∨ rounds.toNat = 14)
    (post := fun ctx rounds state aadLen textLen work tagLen m m' r =>
      let ciph := ctxCiph m ctx rounds.toNat
      let h := ctxH m ctx
      ∀ iv a c, StreamRepr m state ciph h iv a c →
        aadLen = BitVec.ofNat 64 a.length → textLen.toNat = c.length →
        let t := fullTag ciph h iv a c
        if tagLenOk tagLen.toNat ∧ t.take tagLen.toNat = Aes.bytesAt m work tagLen.toNat then
          r = 1 ∧ Aes.bytesAt m' work 16 = t
        else r = 0 ∧ Aes.bytesAt m' work 16 = zeros 16)
    (writeArgs := true)
    (stack := stack)

/-- `vg_aes_gcm_stream_verify` on every target. -/
def streamVerifyApi : Api where
  module := "gcm"
  name := "vg_aes_gcm_stream_verify"
  sig := streamVerifySig
  writeArgs := true
  contracts := some fun A stack => streamVerifyContract A stack
  summary := "Finishes an incremental AES-GCM decryption and checks its tag (NIST SP 800-38D \
    §7.2 steps 6–8): with the key context `*ctx` that `vg_aes_gcm_init` wrote for `rounds` \
    rounds and the received tag in the first `tag_len` bytes of `*work`, if the streaming \
    state `*state` represents a message with `aad_len` bytes of additional data and \
    exactly `text_len` bytes of ciphertext, returns 1 if `tag_len` is 4, 8, 12, 13, 14, \
    15 or 16 (§5.2.1.2) and the received tag is the first `tag_len` bytes of the message's \
    128-bit tag, which it then writes to the first 16 bytes of `*work`; otherwise returns 0 \
    and writes 16 zero bytes there. The rest of `*work` is working space, unspecified on \
    return. The tags are compared without a branch.\n\n\
    Contract: `VG.Spec.Gcm.streamVerifyContract`. Constant time: only the pointers, `rounds`, \
    `aad_len`, `text_len` and `tag_len` may affect timing, not the key context, the state or \
    the tags."
  safety := [
    "`rounds` must be 10, 12 or 14.",
    "The contents of `state` on return are unspecified."]

end VG.Spec.Gcm
