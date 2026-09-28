import VerifiedGarbage.Spec.Sha512
import VerifiedGarbage.TCB.Artifact

/-!
# SHA-512: the contracts, on every target

**Trusted** (as every file in `Spec/`). The contracts of the compression
function and of streaming SHA-384, SHA-512, SHA-512/224 and SHA-512/256
(`init`/`update`/`finalize`, on the representation `Repr`), in terms of
`Spec/Sha512.lean`, for any target: `A` is the target's calling convention.
The signatures fix where the arguments are, the memory each function may
access, disjointness, and that the pointers and lengths are public (see
`TCB/Sig.lean`); the contracts add the postconditions and which other
arguments are public.

`update` and `finalize` take the number of bytes of stack below the stack pointer that
an implementation's calls use (`stack`, see `Sig.contract`), 0 for one that
makes no call: it depends on the target, and on which functions the
implementation calls.
-/

namespace VG.Spec.Sha512

/-- `vg_sha512_compress(state: *mut [u64; 8], blocks: *const [u8; 128], n: usize, scratch: *mut [u64; 28])`.
`scratch` is working space: 224 bytes, enough for every target (the 32-bit
ones need the most, keeping the message schedule, the working variables and
spilled arguments and registers in it). -/
def compressSig : Sig where
  params := [("state", .array true .u64 8), ("blocks", .slice false (.array .u8 128) "n"),
    ("scratch", .array true .u64 28)]

/-- Updates the hash value at `state` with the `n` 128-byte blocks at
`blocks`. The hash value and the blocks are secret. -/
def compressContract {M : ISA} (A : Abi M) : Contract M :=
  compressSig.contract A (post := fun state blocks n _scratch m m' _ =>
    stateAt m' state = compressBlocks (stateAt m state) m blocks n.toNat)

/-- `vg_sha512_compress` on every target. -/
def compressApi : Api where
  module := "sha512"
  name := "vg_sha512_compress"
  sig := compressSig
  summary := "The SHA-512 compression function (FIPS 180-4 §6.4.2), shared by SHA-384, SHA-512, \
    SHA-512/224 and SHA-512/256: updates the hash value `*state` with the `n` 128-byte blocks \
    starting at `blocks`, in order.\n\n\
    Contract: `VG.Spec.Sha512.compressContract`. Constant time: only the pointers and `n` may \
    affect timing, not the hash value or the blocks."
  safety := [
    "`state` must be valid for reads and writes of 64 bytes.",
    "`blocks` must be valid for reads of `128 * n` bytes.",
    "`scratch` must be valid for reads and writes of 224 bytes; its contents on return are \
      unspecified."]

/-- `vg_<alg>_init(state: *mut [u8; 192])`. -/
def initSig : Sig where
  params := [("state", .array true .u8 192)]

/-- Makes the streaming state at `state` represent the empty message, hashed
from `iv`, the initial hash value of `<alg>` (`H0_384`, `H0_512`,
`H0_512_224` or `H0_512_256`). -/
def initContract {M : ISA} (A : Abi M) (iv : HashValue) : Contract M :=
  initSig.contract A (post := fun state _ m' _ => Repr iv m' state [])

/-- `name`, which starts an `alg` computation from its initial hash value
`iv` (the name of `H0_384`, `H0_512`, `H0_512_224` or `H0_512_256`), on
every target. -/
def initApi (alg name iv : String) : Api where
  module := "sha512"
  name := name
  sig := initSig
  summary := s!"Starts a {alg} computation: makes the SHA-512 streaming state `*state` represent \
    the empty message, hashed from the initial hash value of {alg} (`VG.Spec.Sha512.{iv}`). \
    Continue with `vg_sha512_update` and `vg_sha512_finalize`.\n\n\
    Contract: `VG.Spec.Sha512.initContract` for `VG.Spec.Sha512.{iv}`. The streaming state is \
    the hash value followed by a buffered partial block (`VG.Spec.Sha512.Repr`)."
  safety := ["`state` must be valid for writes of 192 bytes."]

def init384Api : Api := initApi "SHA-384" "vg_sha384_init" "H0_384"
def init512Api : Api := initApi "SHA-512" "vg_sha512_init" "H0_512"
def init512_224Api : Api := initApi "SHA-512/224" "vg_sha512_224_init" "H0_512_224"
def init512_256Api : Api := initApi "SHA-512/256" "vg_sha512_256_init" "H0_512_256"

/-- `vg_sha512_update(state: *mut [u8; 192], count: u64, data: *const u8, len: usize, scratch: *mut [u64; 34])`.
`count` is public; `scratch` is working space: 272 bytes, room for the
compression function's scratch (`compressSig`) and the function's own spills. -/
def updateSig : Sig where
  params := [("state", .array true .u8 192), ("count", .int .u64 true),
    ("data", .slice false .u8 "len"), ("scratch", .array true .u64 34)]

/-- If the streaming state at `state` represents a message `msg` of `count`
bytes (modulo 2⁶⁴), hashed from any initial hash value, then afterwards it
represents `msg` followed by the `len` bytes at `data`, from the same one.
The state and the data are secret. -/
def updateContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  updateSig.contract A (post := fun state count data len _scratch m m' _ =>
    ∀ iv msg, Repr iv m state msg → count = BitVec.ofNat 64 msg.length →
      Repr iv m' state (msg ++ bytesAt m data len.toNat))
    (stack := stack)

/-- `vg_sha512_update` on every target. -/
def updateApi : Api where
  module := "sha512"
  name := "vg_sha512_update"
  sig := updateSig
  summary := "Absorbs data into a SHA-384, SHA-512, SHA-512/224 or SHA-512/256 computation: if the \
    streaming state `*state` represents a message of `count` bytes (modulo 2⁶⁴), it then \
    represents that message followed by the `len` bytes at `data`.\n\n\
    Contract: `VG.Spec.Sha512.updateContract`. Constant time: only the pointers, `count` and `len` \
    may affect timing, not the state or the data."
  safety := [
    "`state` must be valid for reads and writes of 192 bytes.",
    "`data` must be valid for reads of `len` bytes.",
    "`scratch` must be valid for reads and writes of 272 bytes; its contents on return are \
      unspecified."]

/-- `vg_sha512_finalize(state: *mut [u8; 192], count: u64, out: *mut [u8; 64], scratch: *mut [u64; 34])`.
`count` is public; `state` is left unspecified, and `scratch` is working
space: 272 bytes, as for `updateSig`. -/
def finalizeSig : Sig where
  params := [("state", .array true .u8 192), ("count", .int .u64 true),
    ("out", .array true .u8 64), ("scratch", .array true .u64 34)]

/-- If the streaming state at `state` represents a message `msg` of `count`
bytes, fewer than 2⁶⁴, hashed from the initial hash value `iv`, writes the
final hash value `H⁽ᴺ⁾` of `msg` from `iv` (64 bytes; `finalHash iv msg`) to
`out`. The digest of SHA-384, SHA-512/224 or SHA-512/256 is its first 48,
28 or 32 bytes. The state is secret. -/
def finalizeContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  finalizeSig.contract A (post := fun state count out _scratch m m' _ =>
    ∀ iv msg, Repr iv m state msg → msg.length < 2 ^ 64 → count = BitVec.ofNat 64 msg.length →
      bytesAt m' out 64 = finalHash iv msg)
    (stack := stack)

/-- `vg_sha512_finalize` on every target. -/
def finalizeApi : Api where
  module := "sha512"
  name := "vg_sha512_finalize"
  sig := finalizeSig
  summary := "Finishes a SHA-384, SHA-512, SHA-512/224 or SHA-512/256 computation: if the \
    streaming state `*state` represents a message of `count` bytes, hashed from an initial hash \
    value, writes the final hash value `H⁽ᴺ⁾` of that message (64 bytes) to `*out`. The SHA-512 \
    digest is all of it; the SHA-384, SHA-512/224 and SHA-512/256 digests are its first 48, 28 and \
    32 bytes.\n\n\
    Contract: `VG.Spec.Sha512.finalizeContract`. Constant time: only the pointers and `count` may \
    affect timing, not the state."
  safety := [
    "`count` must be the exact length of the message: messages of 2⁶⁴ bytes or more are not \
      supported.",
    "`state` must be valid for reads and writes of 192 bytes; its contents on return are \
      unspecified.",
    "`out` must be valid for writes of 64 bytes.",
    "`scratch` must be valid for reads and writes of 272 bytes; its contents on return are \
      unspecified."]

end VG.Spec.Sha512
