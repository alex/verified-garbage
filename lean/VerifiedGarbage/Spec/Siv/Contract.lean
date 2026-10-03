import VerifiedGarbage.Spec.Siv
import VerifiedGarbage.TCB.Artifact

/-!
# AES-SIV: the contracts, on every target

**Trusted** (as every file in `Spec/`). The contracts of AES-SIV, in terms of
`Spec/Siv.lean`, for any target: `A` is the target's calling convention.
The signatures fix where the arguments are, the memory each function may
access, disjointness, and that the pointers, the lengths and the number of
rounds are public (see `TCB/Sig.lean`); the contracts add the rest.
Everything else (keys, key contexts, S2V states, associated data, texts and
synthetic IVs) is secret.

The associated data of SIV is a vector of strings (RFC 5297 §2.6; for
nonce-based encryption the nonce is its last component, §3), which S2V
absorbs one component at a time (§2.4), so the functions are S2V's steps:

* `vg_aes_siv_init` writes a key context (`KeyRepr`): the key schedule of
  `K1`, its CMAC subkeys and the key schedule of `K2`. The others read one,
  with its number of rounds, and compute with the CMAC and the cipher it
  holds (`ctxMac`, `ctxCiph`): with a context `vg_aes_siv_init` wrote, that
  is AES-SIV with its key (`ctxMac_eq`, `ctxCiph_eq`).
* `vg_aes_siv_s2v_start` starts S2V's state `D` (`s2vStart`), and
  `vg_aes_siv_s2v_ad` absorbs one component of associated data into it
  (`s2vStep`): after `s2v_start` and `s2v_ad` of `AD1, …, ADn` in order, `D`
  is `s2vAcc` of them.
* `vg_aes_siv_seal` finishes S2V with the plaintext and encrypts it in place
  (`sealWith`), writing the synthetic IV `V`; from the state of `AD1, …, ADn`,
  that is `SIV-ENCRYPT` (`encryptWith_eq`).
* `vg_aes_siv_open` decrypts the ciphertext in place with the synthetic IV
  it is given, finishes S2V with the plaintext and compares (`openWith`),
  and if they differ overwrites the plaintext with zeros, so that it is
  never released; from the state of `AD1, …, ADn`, that is `SIV-DECRYPT`
  (`decryptWith_eq`). Whether `V` is right is public: `open` may leak it (it
  is the result), and nothing else secret.

`vg_aes_siv_encrypt` and `vg_aes_siv_decrypt` are the whole of
`SIV-ENCRYPT` and `SIV-DECRYPT` (`encryptWith`, `decryptWith`) in one call:
they take the vector of associated data as a list of slices (`Param.slices`,
read by `components`), and run S2V over it themselves. `decrypt` overwrites
the plaintext with zeros if `V` is wrong, and may leak whether it is.

The functions check no length; the RFC limits the associated data to 126
components (§7), which the caller counts. The synthetic IV travels in the
first 16 bytes of `work`, which is also working space, so that fewer
arguments are passed in memory. Each function's working space (`scratch` or
`work`) has room for `vg_aes_ctr32`'s (2048 bytes) and 512 bytes more.

Every contract takes the number of bytes of stack below the stack pointer
that an implementation's calls and frames use (`stack`, see `Sig.contract`),
0 for one that uses none; the functions may overwrite their arguments passed
in memory, where the calling convention allows it (`writeArgs`), to pass
arguments to the functions they call.
-/

namespace VG.Spec.Siv

/-! ## The key context -/

/-- `vg_aes_siv_init(key: *const u8, key_len: usize, ctx: *mut [u64; 64], scratch: *mut [u64; 320])`.
`scratch` is working space. -/
def initSig : Sig where
  params := [("key", .slice false .u8 "key_len"), ("ctx", .array true .u64 64),
    ("scratch", .array true .u64 320)]

/-- For a key of 32, 48 or 64 bytes at `key`, makes the 512 bytes at `ctx`
its key context (`KeyRepr`). -/
def initContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  initSig.contract A
    (pre := fun _key keyLen _ctx _scratch _ =>
      keyLen.toNat = 32 ∨ keyLen.toNat = 48 ∨ keyLen.toNat = 64)
    (post := fun key keyLen ctx _scratch m m' _ => KeyRepr m' ctx (Aes.bytesAt m key keyLen.toNat))
    (writeArgs := true)
    (stack := stack)

/-- `vg_aes_siv_init` on every target. -/
def initApi : Api where
  module := "aes_siv"
  name := "vg_aes_siv_init"
  sig := initSig
  writeArgs := true
  contracts := some fun A stack => initContract A stack
  summary := "The AES-SIV key setup (RFC 5297 §2.6): writes the key context of the \
    `key_len`-byte key `K = K1 ‖ K2` at `key` (the halves of `key_len / 2` bytes) to `*ctx`: \
    the key schedule of `K1` for `Nr = key_len / 8 + 6` rounds (FIPS 197 §5.2, as \
    `vg_aes_expand_key` writes it) in the first `16 * (Nr + 1)` bytes, its CMAC subkeys \
    (NIST SP 800-38B §6.1) in bytes 240–271, and the key schedule of `K2` in the \
    `16 * (Nr + 1)` bytes from byte 272. The other bytes are unspecified. The other \
    `vg_aes_siv_*` functions read it, with `Nr` as their `rounds`.\n\n\
    Contract: `VG.Spec.Siv.initContract`. The key context is `VG.Spec.Siv.KeyRepr`. Constant \
    time: only the pointers and `key_len` may affect timing, not the key."
  safety := [
    "`key_len` must be 32, 48 or 64.",
    "The contents of `scratch` on return are unspecified."]

/-! ## S2V of the associated data -/

/-- `vg_aes_siv_s2v_start(ctx: *const [u64; 64], rounds: usize, d: *mut [u8; 16], scratch: *mut [u64; 320])`.
`rounds` is public; `scratch` is working space. -/
def s2vStartSig : Sig where
  params := [("ctx", .array false .u64 64), ("rounds", .int .usize true),
    ("d", .array true .u8 16), ("scratch", .array true .u64 320)]

/-- For `rounds` of 10, 12 or 14, with the key context at `ctx`: writes the
first state of S2V, `D = AES-CMAC(K1, <zero>)`, to `d`. -/
def s2vStartContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  s2vStartSig.contract A
    (pre := fun _ctx rounds _d _scratch _ =>
      rounds.toNat = 10 ∨ rounds.toNat = 12 ∨ rounds.toNat = 14)
    (post := fun ctx rounds d _scratch m m' _ =>
      Aes.bytesAt m' d 16 = s2vStart (ctxMac m ctx rounds.toNat))
    (writeArgs := true)
    (stack := stack)

/-- `vg_aes_siv_s2v_start` on every target. -/
def s2vStartApi : Api where
  module := "aes_siv"
  name := "vg_aes_siv_s2v_start"
  sig := s2vStartSig
  writeArgs := true
  contracts := some fun A stack => s2vStartContract A stack
  summary := "Starts S2V (RFC 5297 §2.4) for an AES-SIV encryption or decryption: with the key \
    context `*ctx` that `vg_aes_siv_init` wrote for `rounds` rounds, writes \
    `D = AES-CMAC(K1, <zero>)` to `*d`. Continue with `vg_aes_siv_s2v_ad` for each component \
    of the associated data (the nonce last, for nonce-based encryption), then \
    `vg_aes_siv_seal` or `vg_aes_siv_open`, with the same key context.\n\n\
    Contract: `VG.Spec.Siv.s2vStartContract`. Constant time: only the pointers and `rounds` \
    may affect timing, not the key context."
  safety := [
    "`rounds` must be 10, 12 or 14.",
    "The contents of `scratch` on return are unspecified."]

/-- `vg_aes_siv_s2v_ad(ctx: *const [u64; 64], rounds: usize, d: *mut [u8; 16], data: *const u8, len: usize, scratch: *mut [u64; 320])`.
`rounds` is public; `scratch` is working space. -/
def s2vAdSig : Sig where
  params := [("ctx", .array false .u64 64), ("rounds", .int .usize true),
    ("d", .array true .u8 16), ("data", .slice false .u8 "len"),
    ("scratch", .array true .u64 320)]

/-- For `rounds` of 10, 12 or 14, with the key context at `ctx`: replaces the
state `D` at `d` with `dbl(D) xor AES-CMAC(K1, S)` for the component `S`,
the `len` bytes at `data` (`s2vStep`). -/
def s2vAdContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  s2vAdSig.contract A
    (pre := fun _ctx rounds _d _data _len _scratch _ =>
      rounds.toNat = 10 ∨ rounds.toNat = 12 ∨ rounds.toNat = 14)
    (post := fun ctx rounds d data len _scratch m m' _ =>
      Aes.bytesAt m' d 16 =
        s2vStep (ctxMac m ctx rounds.toNat) (Aes.bytesAt m d 16) (Aes.bytesAt m data len.toNat))
    (writeArgs := true)
    (stack := stack)

/-- `vg_aes_siv_s2v_ad` on every target. -/
def s2vAdApi : Api where
  module := "aes_siv"
  name := "vg_aes_siv_s2v_ad"
  sig := s2vAdSig
  writeArgs := true
  contracts := some fun A stack => s2vAdContract A stack
  summary := "Absorbs one component of associated data into S2V (RFC 5297 §2.4's loop): with \
    the key context `*ctx` that `vg_aes_siv_init` wrote for `rounds` rounds, replaces the S2V \
    state `D` in `*d` with `dbl(D) xor AES-CMAC(K1, S)`, where the component `S` is the `len` \
    bytes at `data`. RFC 5297 allows at most 126 components (§7), which the caller must \
    count.\n\n\
    Contract: `VG.Spec.Siv.s2vAdContract`. Constant time: only the pointers, `rounds` and `len` \
    may affect timing, not the key context, the state or the data."
  safety := [
    "`rounds` must be 10, 12 or 14.",
    "The contents of `scratch` on return are unspecified."]

/-! ## Encryption and decryption -/

/-- `vg_aes_siv_seal(ctx: *const [u64; 64], rounds: usize, d: *const [u8; 16], data: *mut u8, len: usize, work: *mut [u64; 320])`,
and `vg_aes_siv_open` with the same parameters, returning a `u32`. `rounds`
is public; `work` is working space but for the synthetic IV. -/
def sealSig : Sig where
  params := [("ctx", .array false .u64 64), ("rounds", .int .usize true),
    ("d", .array false .u8 16), ("data", .slice true .u8 "len"),
    ("work", .array true .u64 320)]

/-- `vg_aes_siv_open`'s signature: `vg_aes_siv_seal`'s, returning a `u32`. -/
def openSig : Sig := { sealSig with ret := some .u32 }

/-- For `rounds` of 10, 12 or 14, with the key context at `ctx` and the S2V
state `D` of the associated data at `d`: encrypts the `len` bytes of
plaintext at `data` in place (`sealWith`) and writes the synthetic IV `V` to
the first 16 bytes of `work`. -/
def sealContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  sealSig.contract A
    (pre := fun _ctx rounds _d _data _len _work _ =>
      rounds.toNat = 10 ∨ rounds.toNat = 12 ∨ rounds.toNat = 14)
    (post := fun ctx rounds d data len work m m' _ =>
      sealWith (ctxMac m ctx rounds.toNat) (ctxCiph m ctx rounds.toNat) (Aes.bytesAt m d 16)
          (Aes.bytesAt m data len.toNat) =
        (Aes.bytesAt m' work 16, Aes.bytesAt m' data len.toNat))
    (writeArgs := true)
    (stack := stack)

/-- `vg_aes_siv_seal` on every target. -/
def sealApi : Api where
  module := "aes_siv"
  name := "vg_aes_siv_seal"
  sig := sealSig
  writeArgs := true
  contracts := some fun A stack => sealContract A stack
  summary := "AES-SIV encryption (RFC 5297 §2.6), after S2V of the associated data: with the key \
    context `*ctx` that `vg_aes_siv_init` wrote for `rounds` rounds and the S2V state `*d` of \
    the associated data (`vg_aes_siv_s2v_start`, then `vg_aes_siv_s2v_ad` of each component), \
    finishes S2V with the `len` bytes of plaintext at `data`, writing the synthetic IV `V` to \
    the first 16 bytes of `*work`, and encrypts the plaintext in place with AES-CTR under `K2` \
    from `V` with bits 31 and 63 cleared. The RFC's output is `V` followed by the encrypted \
    data. The rest of `*work` is working space, unspecified on return.\n\n\
    Contract: `VG.Spec.Siv.sealContract`. Constant time: only the pointers, `rounds` and `len` \
    may affect timing, not the key context, the state or the data."
  safety := ["`rounds` must be 10, 12 or 14."]

/-- For `rounds` of 10, 12 or 14, with the key context at `ctx`, the S2V
state `D` of the associated data at `d` and the received synthetic IV `V`
in the first 16 bytes of `work`: if `V` is right for the plaintext of the
`len` bytes of ciphertext at `data` (`openWith`), returns 1 and leaves the
plaintext at `data`; otherwise returns 0 and leaves zeros at `data`. May
leak which (`openWith`'s outcome). -/
def openContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  openSig.contract A
    (pre := fun _ctx rounds _d _data _len _work _ =>
      rounds.toNat = 10 ∨ rounds.toNat = 12 ∨ rounds.toNat = 14)
    (post := fun ctx rounds d data len work m m' r =>
      match openWith (ctxMac m ctx rounds.toNat) (ctxCiph m ctx rounds.toNat) (Aes.bytesAt m d 16)
          (Aes.bytesAt m work 16) (Aes.bytesAt m data len.toNat) with
      | some pt => r = 1 ∧ Aes.bytesAt m' data len.toNat = pt
      | none => r = 0 ∧ Aes.bytesAt m' data len.toNat = zeros len.toNat)
    (writeArgs := true)
    (stack := stack)
    (leak := some fun ctx rounds d data len work m =>
      [if (openWith (ctxMac m ctx rounds.toNat) (ctxCiph m ctx rounds.toNat) (Aes.bytesAt m d 16)
          (Aes.bytesAt m work 16) (Aes.bytesAt m data len.toNat)).isSome
        then 1 else 0])

/-- `vg_aes_siv_open` on every target. -/
def openApi : Api where
  module := "aes_siv"
  name := "vg_aes_siv_open"
  sig := openSig
  writeArgs := true
  contracts := some fun A stack => openContract A stack
  summary := "AES-SIV decryption (RFC 5297 §2.7), after S2V of the associated data: with the key \
    context `*ctx` that `vg_aes_siv_init` wrote for `rounds` rounds, the S2V state `*d` of the \
    associated data (`vg_aes_siv_s2v_start`, then `vg_aes_siv_s2v_ad` of each component) and \
    the received synthetic IV `V` in the first 16 bytes of `*work`, decrypts the `len` bytes \
    of ciphertext at `data` in place with AES-CTR under `K2` from `V` with bits 31 and 63 \
    cleared, finishes S2V with the plaintext, and returns 1 if the result is `V`; otherwise \
    returns 0 and overwrites the `len` bytes at `data` with zeros. The rest of `*work` is \
    working space, unspecified on return. The IVs are compared without a branch.\n\n\
    Contract: `VG.Spec.Siv.openContract`. Constant time but for the result: only the pointers, \
    `rounds`, `len` and whether the function returns 1 or 0 may affect timing, not the key \
    context, the state, the data or `V`."
  safety := ["`rounds` must be 10, 12 or 14."]

/-! ## Encryption and decryption in one call -/

/-- The components of associated data that the `n` descriptors at `p` list
in the memory `m`, on a target with `ptrBits`-bit pointers: the bytes of
each slice `Sig.listed` gives, in order. -/
def components (ptrBits : Nat) (m : Mem) (p : Addr) (n : Nat) : List (List Byte) :=
  (Sig.listed ptrBits m .u8 p n).map fun r => Aes.bytesAt m r.base r.len

/-- `vg_aes_siv_encrypt(ctx: *const [u64; 64], rounds: usize, ads: *const [usize; 2], ads_count: usize, data: *mut u8, len: usize, work: *mut [u64; 320])`,
and `vg_aes_siv_decrypt` with the same parameters, returning a `u32`.
`rounds` is public; `ads` lists the components of associated data; `work`
is working space but for the synthetic IV. -/
def encryptSig : Sig where
  params := [("ctx", .array false .u64 64), ("rounds", .int .usize true),
    ("ads", .slices .u8 "ads_count"), ("data", .slice true .u8 "len"),
    ("work", .array true .u64 320)]

/-- `vg_aes_siv_decrypt`'s signature: `vg_aes_siv_encrypt`'s, returning a `u32`. -/
def decryptSig : Sig := { encryptSig with ret := some .u32 }

/-- For `rounds` of 10, 12 or 14, with the key context at `ctx` and the
components of associated data `ads` lists (`components`): encrypts the `len`
bytes of plaintext at `data` in place (`encryptWith`) and writes the
synthetic IV `V` to the first 16 bytes of `work`. -/
def encryptContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  encryptSig.contract A
    (pre := fun _ctx rounds _ads _adsCount _data _len _work _ =>
      rounds.toNat = 10 ∨ rounds.toNat = 12 ∨ rounds.toNat = 14)
    (post := fun ctx rounds ads adsCount data len work m m' _ =>
      encryptWith (ctxMac m ctx rounds.toNat) (ctxCiph m ctx rounds.toNat)
          (components A.ptrBits m ads adsCount.toNat) (Aes.bytesAt m data len.toNat) =
        (Aes.bytesAt m' work 16, Aes.bytesAt m' data len.toNat))
    (writeArgs := true)
    (stack := stack)

/-- `vg_aes_siv_encrypt` on every target. -/
def encryptApi : Api where
  module := "aes_siv"
  name := "vg_aes_siv_encrypt"
  sig := encryptSig
  writeArgs := true
  contracts := some fun A stack => encryptContract A stack
  summary := "AES-SIV encryption, `SIV-ENCRYPT` (RFC 5297 §2.6): with the key context `*ctx` \
    that `vg_aes_siv_init` wrote for `rounds` rounds, computes the synthetic IV \
    `V = S2V(K1, AD1, …, ADn, P)` of the `ads_count` components of associated data that \
    `ads` lists (each an address and a length, in bytes; for nonce-based encryption, §3, the \
    nonce is the last) and the `len` bytes of plaintext `P` at `data`, writes it to the first \
    16 bytes of `*work`, and encrypts the plaintext in place with AES-CTR under `K2` from `V` \
    with bits 31 and 63 cleared. The RFC's output is `V` followed by the encrypted data. The \
    rest of `*work` is working space, unspecified on return.\n\n\
    Contract: `VG.Spec.Siv.encryptContract`. Constant time: only the pointers, `rounds`, \
    `ads_count`, `len` and where the components are (their addresses and lengths) may affect \
    timing, not the key context, the associated data or the plaintext."
  safety := ["`rounds` must be 10, 12 or 14."]

/-- For `rounds` of 10, 12 or 14, with the key context at `ctx`, the
components of associated data `ads` lists and the received synthetic IV `V`
in the first 16 bytes of `work`: if `V` is right for the plaintext of the
`len` bytes of ciphertext at `data` (`decryptWith`), returns 1 and leaves the
plaintext at `data`; otherwise returns 0 and leaves zeros at `data`. May leak
which (`decryptWith`'s outcome). -/
def decryptContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  decryptSig.contract A
    (pre := fun _ctx rounds _ads _adsCount _data _len _work _ =>
      rounds.toNat = 10 ∨ rounds.toNat = 12 ∨ rounds.toNat = 14)
    (post := fun ctx rounds ads adsCount data len work m m' r =>
      match decryptWith (ctxMac m ctx rounds.toNat) (ctxCiph m ctx rounds.toNat)
          (components A.ptrBits m ads adsCount.toNat) (Aes.bytesAt m work 16)
          (Aes.bytesAt m data len.toNat) with
      | some pt => r = 1 ∧ Aes.bytesAt m' data len.toNat = pt
      | none => r = 0 ∧ Aes.bytesAt m' data len.toNat = zeros len.toNat)
    (writeArgs := true)
    (stack := stack)
    (leak := some fun ctx rounds ads adsCount data len work m =>
      [if (decryptWith (ctxMac m ctx rounds.toNat) (ctxCiph m ctx rounds.toNat)
          (components A.ptrBits m ads adsCount.toNat) (Aes.bytesAt m work 16)
          (Aes.bytesAt m data len.toNat)).isSome
        then 1 else 0])

/-- `vg_aes_siv_decrypt` on every target. -/
def decryptApi : Api where
  module := "aes_siv"
  name := "vg_aes_siv_decrypt"
  sig := decryptSig
  writeArgs := true
  contracts := some fun A stack => decryptContract A stack
  summary := "AES-SIV decryption, `SIV-DECRYPT` (RFC 5297 §2.7): with the key context `*ctx` \
    that `vg_aes_siv_init` wrote for `rounds` rounds and the received synthetic IV `V` in the \
    first 16 bytes of `*work`, decrypts the `len` bytes of ciphertext at `data` in place with \
    AES-CTR under `K2` from `V` with bits 31 and 63 cleared, computes \
    `S2V(K1, AD1, …, ADn, P)` of the `ads_count` components of associated data that `ads` \
    lists (each an address and a length, in bytes) and the plaintext `P`, and returns 1 if it \
    is `V`; otherwise returns 0 and overwrites the `len` bytes at `data` with zeros. The rest \
    of `*work` is working space, unspecified on return. The IVs are compared without a \
    branch.\n\n\
    Contract: `VG.Spec.Siv.decryptContract`. Constant time but for the result: only the \
    pointers, `rounds`, `ads_count`, `len`, where the components are (their addresses and \
    lengths) and whether the function returns 1 or 0 may affect timing, not the key context, \
    the associated data, the data or `V`."
  safety := ["`rounds` must be 10, 12 or 14."]

end VG.Spec.Siv
