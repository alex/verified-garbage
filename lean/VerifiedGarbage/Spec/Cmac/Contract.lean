import VerifiedGarbage.Spec.Cmac
import VerifiedGarbage.TCB.Artifact

/-!
# AES-CMAC: the contracts, on every target

**Trusted** (as every file in `Spec/`). The contracts of the three
primitives AES-CMAC is built from, and of streaming AES-CMAC, in terms of
`Spec/Cmac.lean`, for any target: `A` is the target's calling convention.
The signatures fix where the arguments are, the memory each function may
access, disjointness, and that the pointers, the lengths and the number of
rounds are public (see `TCB/Sig.lean`). The key schedule, the subkeys, the
chaining value and the message are secret.

Each of the three primitives reads the AES key schedule that `vg_aes_expand_key`
(`VG.Spec.Aes.expandKeyContract`) writes, `16 (rounds + 1)` bytes, at the
start of a 240-byte buffer.

* `vg_cmac_aes_subkeys` writes the subkeys `K1 ‖ K2` (§6.1).
* `vg_cmac_aes_update` continues §6.2 step 6 (`Cᵢ = CIPH_K(Cᵢ₋₁ ⊕ Mᵢ)`)
  over whole blocks, from the chaining value `C` in `state`.
* `vg_cmac_aes_finalize` takes the key schedule and the subkeys together,
  as one 272-byte buffer (the 240-byte schedule buffer, then `K1 ‖ K2`),
  and the message's last bytes `Mₙ*` (at most a block); if `state` holds the
  chaining value of the message's other blocks, it replaces it with the
  MAC of the whole message (§6.2, with `Tlen = 128`).

The Rust caller of these three keeps the chaining value between calls, and
holds back the last block of what it has been given, even a complete one,
since only `finalize` knows whether a block is the last (§6.2 step 4); it
calls `finalize` with no bytes only for the empty message.

Streaming AES-CMAC does all of that in a state of its own (`Repr`, in
`Spec/Cmac.lean`), which the caller holds as opaque words:

* `vg_cmac_aes_init` expands a key of 16, 24 or 32 bytes into the state
  (the key schedule and the subkeys) and makes it represent the empty
  message (§6.2 steps 1 and 5).
* `vg_cmac_aes_absorb` absorbs bytes of any length, chaining every block but
  the last bytes `Mₙ*`, which it holds back in the state (steps 3 and 6).
* `vg_cmac_aes_finish` writes the MAC of the message the state represents
  (steps 4 and 6, with `Tlen = 128`).

The key length is public, so the number of rounds is; the length of the
message so far (`count`) is public, as the lengths of its pieces are, so
the number of bytes held back (a function of it) is too. The key, the
state and the message are secret. `absorb` and `finish` take the number of
rounds (`key_len / 4 + 6` for the key `init` was given) and `count` from
the caller, as the hashes' `update` and `finalize` take `count`: the state
does not store them, since what it stores is secret. Every message is
shorter than 2⁶⁴ bytes, so that `count` (a `u64`) is its exact length: with
a length modulo 2⁶⁴, a message of 2⁶⁴ bytes, whose last block is held back,
would look like the empty one.

The caller truncates the MAC and compares MACs (§6.3).

Each takes a `scratch` buffer of working space, sized for the target that
needs the most (the first three: room for `vg_aes_ctr32`'s working space
and 128 bytes more; the streaming functions: room for theirs and 128 bytes
more), and the number of bytes of stack below the stack pointer that an
implementation's calls and frames use (`stack`, see `Sig.contract`), 0 for
one that uses none.
-/

namespace VG.Spec.Cmac

/-- `vg_cmac_aes_subkeys(schedule: *const [u8; 240], rounds: usize, subkeys: *mut [u8; 32], scratch: *mut [u64; 272])`.
`rounds` is public; `scratch` is working space. -/
def aesSubkeysSig : Sig where
  params := [("schedule", .array false .u8 240), ("rounds", .int .usize true),
    ("subkeys", .array true .u8 32), ("scratch", .array true .u64 272)]

/-- For `rounds` of 10, 12 or 14, with the key schedule `w` in the first
`16 (rounds + 1)` bytes at `schedule`: writes the subkeys `K1 ‖ K2` of AES
with that schedule (§6.1) to `subkeys`. -/
def aesSubkeysContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  aesSubkeysSig.contract A
    (pre := fun _schedule rounds _subkeys _scratch _ =>
      rounds.toNat = 10 ∨ rounds.toNat = 12 ∨ rounds.toNat = 14)
    (post := fun schedule rounds subkeys' _scratch m m' _ =>
      let ks := subkeys (aesWith rounds.toNat (Aes.bytesAt m schedule (16 * (rounds.toNat + 1)))) 16
      Aes.bytesAt m' subkeys' 32 = ks.1 ++ ks.2)
    (stack := stack)

/-- `vg_cmac_aes_subkeys` on every target. -/
def aesSubkeysApi : Api where
  module := "cmac_aes"
  name := "vg_cmac_aes_subkeys"
  sig := aesSubkeysSig
  contracts := some fun A stack => aesSubkeysContract A stack
  summary := "The CMAC subkey generation (NIST SP 800-38B §6.1) for AES: writes `K1 ‖ K2` to \
    `*subkeys`, where `L = CIPH_K(0¹²⁸)`, `K1 = L << 1` (XORed with `R₁₂₈ = 0¹²⁰10000111` if \
    the leftmost bit of `L` is 1) and `K2` is `K1` doubled the same way. `CIPH_K` is AES \
    (FIPS 197) with `rounds` rounds and the key schedule in the first `16 * (rounds + 1)` \
    bytes of `*schedule`, as `vg_aes_expand_key` writes it.\n\n\
    Contract: `VG.Spec.Cmac.aesSubkeysContract`. Constant time: only the pointers and `rounds` \
    may affect timing, not the key schedule or the subkeys."
  safety := [
    "`rounds` must be 10, 12 or 14.",
    "The contents of `scratch` on return are unspecified."]

/-- `vg_cmac_aes_update(schedule: *const [u8; 240], rounds: usize, state: *mut [u8; 16], data: *const [u8; 16], n: usize, scratch: *mut [u64; 272])`.
`rounds` is public; `scratch` is working space. -/
def aesUpdateSig : Sig where
  params := [("schedule", .array false .u8 240), ("rounds", .int .usize true),
    ("state", .array true .u8 16), ("data", .slice false (.array .u8 16) "n"),
    ("scratch", .array true .u64 272)]

/-- For `rounds` of 10, 12 or 14, with the key schedule `w` in the first
`16 (rounds + 1)` bytes at `schedule`: replaces the block `C` at `state`
with §6.2 step 6 continued from `C` over the `n` blocks at `data`. -/
def aesUpdateContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  aesUpdateSig.contract A
    (pre := fun _schedule rounds _state _data _n _scratch _ =>
      rounds.toNat = 10 ∨ rounds.toNat = 12 ∨ rounds.toNat = 14)
    (post := fun schedule rounds state data n _scratch m m' _ =>
      let ciph := aesWith rounds.toNat (Aes.bytesAt m schedule (16 * (rounds.toNat + 1)))
      Aes.bytesAt m' state 16 = chain ciph (Aes.bytesAt m state 16) (blocksAt m data 16 n.toNat))
    (stack := stack)

/-- `vg_cmac_aes_update` on every target. -/
def aesUpdateApi : Api where
  module := "cmac_aes"
  name := "vg_cmac_aes_update"
  sig := aesUpdateSig
  contracts := some fun A stack => aesUpdateContract A stack
  summary := "CMAC's chaining (NIST SP 800-38B §6.2 step 6) for AES, over whole blocks: replaces \
    the block `C₀` at `*state` with `Cₙ`, where `Cᵢ = CIPH_K(Cᵢ₋₁ ⊕ Mᵢ)` for the `n` 16-byte \
    blocks `M₁ … Mₙ` starting at `data`. `CIPH_K` is AES (FIPS 197) with `rounds` rounds and \
    the key schedule in the first `16 * (rounds + 1)` bytes of `*schedule`, as \
    `vg_aes_expand_key` writes it.\n\n\
    Contract: `VG.Spec.Cmac.aesUpdateContract`. Constant time: only the pointers, `rounds` and \
    `n` may affect timing, not the key schedule, the chaining value or the data."
  safety := [
    "`rounds` must be 10, 12 or 14.",
    "The contents of `scratch` on return are unspecified."]

/-- `vg_cmac_aes_finalize(key: *const [u8; 272], rounds: usize, state: *mut [u8; 16], last: *const u8, last_len: usize, scratch: *mut [u64; 272])`.
`rounds` is public; `scratch` is working space. -/
def aesFinalizeSig : Sig where
  params := [("key", .array false .u8 272), ("rounds", .int .usize true),
    ("state", .array true .u8 16), ("last", .slice false .u8 "last_len"),
    ("scratch", .array true .u64 272)]

/-- For `rounds` of 10, 12 or 14 and `last_len` at most 16, with the key
schedule `w` in the first `16 (rounds + 1)` bytes at `key` and AES's
subkeys `K1 ‖ K2` for it in bytes 240–271: if the block at `state` is the
chaining value (§6.2 step 6, from `C₀ = 0¹²⁸`) of a message `msg` of whole
blocks, and `last_len` is not 0 unless `msg` is empty (so that the `last_len`
bytes at `last` are `Mₙ*`), replaces it with the CMAC `Cₙ` of `msg`
followed by those bytes. -/
def aesFinalizeContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  aesFinalizeSig.contract A
    (pre := fun _key rounds _state _last lastLen _scratch _ =>
      (rounds.toNat = 10 ∨ rounds.toNat = 12 ∨ rounds.toNat = 14) ∧ lastLen.toNat ≤ 16)
    (post := fun key rounds state last lastLen _scratch m m' _ =>
      let ciph := aesWith rounds.toNat (Aes.bytesAt m key (16 * (rounds.toNat + 1)))
      let ks := subkeys ciph 16
      Aes.bytesAt m (key + 240) 32 = ks.1 ++ ks.2 →
      ∀ msg : List Byte, msg.length % 16 = 0 → (msg = [] ∨ 0 < lastLen.toNat) →
        Aes.bytesAt m state 16 = chain ciph (zeros 16) (blocks 16 msg) →
        Aes.bytesAt m' state 16 = macFull ciph 16 (msg ++ Aes.bytesAt m last lastLen.toNat))
    (stack := stack)

/-- `vg_cmac_aes_finalize` on every target. -/
def aesFinalizeApi : Api where
  module := "cmac_aes"
  name := "vg_cmac_aes_finalize"
  sig := aesFinalizeSig
  contracts := some fun A stack => aesFinalizeContract A stack
  summary := "Finishes an AES-CMAC computation (NIST SP 800-38B §6.2, with `Tlen = 128`): if the \
    block at `*state` is the chaining value `Cₙ₋₁` of the message's blocks but the last (as \
    `vg_cmac_aes_update` computes it from a zero block), and the `last_len` bytes at `last` are \
    the message's last bytes `Mₙ*`, replaces it with the MAC `Cₙ = CIPH_K(Cₙ₋₁ ⊕ Mₙ)`, where \
    `Mₙ = K1 ⊕ Mₙ*` if `last_len` is 16, and `Mₙ = K2 ⊕ (Mₙ* ‖ 10ʲ)` otherwise. `*key` is the \
    240 bytes `vg_aes_expand_key` writes the key schedule for `rounds` rounds to, followed by \
    the subkeys `K1 ‖ K2` (as `vg_cmac_aes_subkeys` writes them). `last_len` is 0 only for \
    the empty message.\n\n\
    Contract: `VG.Spec.Cmac.aesFinalizeContract`. Constant time: only the pointers, `rounds` \
    and `last_len` may affect timing, not the key schedule, the subkeys, the chaining value or \
    the data."
  safety := [
    "`rounds` must be 10, 12 or 14.",
    "`last_len` must be at most 16.",
    "The contents of `scratch` on return are unspecified."]

/-! ## Streaming AES-CMAC -/

/-- `vg_cmac_aes_init(state: *mut [u64; 38], key: *const u8, key_len: usize, scratch: *mut [u64; 288])`.
`scratch` is working space. -/
def aesInitSig : Sig where
  params := [("state", .array true .u64 38), ("key", .slice false .u8 "key_len"),
    ("scratch", .array true .u64 288)]

/-- For a key of 16, 24 or 32 bytes at `key`: makes the state at `state`
represent the empty message under that key. The key is secret. -/
def aesInitContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  aesInitSig.contract A
    (pre := fun _state _key keyLen _scratch _ =>
      keyLen.toNat = 16 ∨ keyLen.toNat = 24 ∨ keyLen.toNat = 32)
    (post := fun state key keyLen _scratch m m' _ =>
      Repr m' state (Aes.bytesAt m key keyLen.toNat) [])
    (stack := stack)

/-- `vg_cmac_aes_init` on every target. -/
def aesInitApi : Api where
  module := "cmac_aes"
  name := "vg_cmac_aes_init"
  sig := aesInitSig
  contracts := some fun A stack => aesInitContract A stack
  summary := "Starts an AES-CMAC computation (NIST SP 800-38B, RFC 4493): makes the streaming \
    state `*state` represent the empty message under the AES key of `key_len` bytes at `key` \
    (AES-128, AES-192 or AES-256). The state holds the key schedule of AES (FIPS 197) with \
    `key_len / 4 + 6` rounds, the subkeys `K1 ‖ K2` (§6.1), the chaining value and the \
    message's last bytes, held back (`VG.Spec.Cmac.Repr`). Continue with `vg_cmac_aes_absorb` \
    and `vg_cmac_aes_finish`, passing them `key_len / 4 + 6` as `rounds`.\n\n\
    Contract: `VG.Spec.Cmac.aesInitContract`. Constant time: only the pointers and `key_len` may \
    affect timing, not the key."
  safety := [
    "`key_len` must be 16, 24 or 32.",
    "The contents of `scratch` on return are unspecified."]

/-- `vg_cmac_aes_absorb(state: *mut [u64; 38], rounds: usize, count: u64, data: *const u8, len: usize, scratch: *mut [u64; 288])`.
`rounds` and `count` are public; `scratch` is working space. -/
def aesAbsorbSig : Sig where
  params := [("state", .array true .u64 38), ("rounds", .int .usize true),
    ("count", .int .u64 true), ("data", .slice false .u8 "len"),
    ("scratch", .array true .u64 288)]

/-- For `rounds` of 10, 12 or 14: if the state at `state` represents a
message `msg` of `count` bytes under a key of `Nr = rounds` rounds, and
`msg` followed by the `len` bytes at `data` is shorter than 2⁶⁴ bytes, then
afterwards it represents `msg` followed by those bytes, under the same key.
The state and the data are secret. -/
def aesAbsorbContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  aesAbsorbSig.contract A
    (pre := fun _state rounds _count _data _len _scratch _ =>
      rounds.toNat = 10 ∨ rounds.toNat = 12 ∨ rounds.toNat = 14)
    (post := fun state rounds count data len _scratch m m' _ =>
      ∀ key msg, Repr m state key msg → rounds.toNat = Aes.rounds (key.length / 4) →
        count = BitVec.ofNat 64 msg.length → msg.length + len.toNat < 2 ^ 64 →
        Repr m' state key (msg ++ Aes.bytesAt m data len.toNat))
    (stack := stack)

/-- `vg_cmac_aes_absorb` on every target. -/
def aesAbsorbApi : Api where
  module := "cmac_aes"
  name := "vg_cmac_aes_absorb"
  sig := aesAbsorbSig
  contracts := some fun A stack => aesAbsorbContract A stack
  summary := "Absorbs data into an AES-CMAC computation (NIST SP 800-38B §6.2): if the streaming \
    state `*state` represents a message of `count` bytes under an AES key with `rounds` rounds \
    (as `vg_cmac_aes_init` set it up), it then represents that message followed by the `len` \
    bytes at `data`, under the same key, provided that the two together are shorter than 2⁶⁴ \
    bytes. It chains (step 6) every block of the message but its last bytes `Mₙ*` (step 3), \
    which it holds back in the state, since only `vg_cmac_aes_finish` knows they are the last.\n\n\
    Contract: `VG.Spec.Cmac.aesAbsorbContract`. Constant time: only the pointers, `rounds`, \
    `count` and `len` may affect timing, not the state or the data."
  safety := [
    "`rounds` must be 10, 12 or 14.",
    "The contents of `scratch` on return are unspecified."]

/-- `vg_cmac_aes_finish(state: *mut [u64; 38], rounds: usize, count: u64, out: *mut [u8; 16], scratch: *mut [u64; 288])`.
`rounds` and `count` are public; `state` is left unspecified, and `scratch`
is working space. -/
def aesFinishSig : Sig where
  params := [("state", .array true .u64 38), ("rounds", .int .usize true),
    ("count", .int .u64 true), ("out", .array true .u8 16),
    ("scratch", .array true .u64 288)]

/-- For `rounds` of 10, 12 or 14: if the state at `state` represents a
message `msg` of `count` bytes, shorter than 2⁶⁴ bytes, under a key `key`
of `Nr = rounds` rounds, writes the AES-CMAC of `msg` under `key` (§6.2,
with `Tlen = 128`) to `out`. The state is secret. -/
def aesFinishContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  aesFinishSig.contract A
    (pre := fun _state rounds _count _out _scratch _ =>
      rounds.toNat = 10 ∨ rounds.toNat = 12 ∨ rounds.toNat = 14)
    (post := fun state rounds count out _scratch m m' _ =>
      ∀ key msg, Repr m state key msg → rounds.toNat = Aes.rounds (key.length / 4) →
        count = BitVec.ofNat 64 msg.length → msg.length < 2 ^ 64 →
        Aes.bytesAt m' out 16 = aesCmac key 16 msg)
    (stack := stack)

/-- `vg_cmac_aes_finish` on every target. -/
def aesFinishApi : Api where
  module := "cmac_aes"
  name := "vg_cmac_aes_finish"
  sig := aesFinishSig
  contracts := some fun A stack => aesFinishContract A stack
  summary := "Finishes an AES-CMAC computation (NIST SP 800-38B §6.2, with `Tlen = 128`): if the \
    streaming state `*state` represents a message of `count` bytes, shorter than 2⁶⁴ bytes, \
    under an AES key with `rounds` rounds (as `vg_cmac_aes_init` and `vg_cmac_aes_absorb` set \
    it up), writes the MAC of that message under that key to `*out`: `Cₙ = CIPH_K(Cₙ₋₁ ⊕ Mₙ)`, \
    where `Mₙ = K1 ⊕ Mₙ*` if the message's last bytes `Mₙ*` are a complete block, and \
    `Mₙ = K2 ⊕ (Mₙ* ‖ 10ʲ)` otherwise (step 4). The caller truncates it (step 7) and compares \
    it (§6.3).\n\n\
    Contract: `VG.Spec.Cmac.aesFinishContract`. Constant time: only the pointers, `rounds` and \
    `count` may affect timing, not the state."
  safety := [
    "`rounds` must be 10, 12 or 14.",
    "The contents of `state` on return are unspecified.",
    "The contents of `scratch` on return are unspecified."]

end VG.Spec.Cmac
