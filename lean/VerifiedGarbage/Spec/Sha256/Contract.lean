import VerifiedGarbage.Spec.Sha256
import VerifiedGarbage.TCB.Artifact

/-!
# SHA-256: the contracts, on every target

**Trusted** (as every file in `Spec/`). The contracts of the compression
function and of streaming SHA-256 (`init`/`update`/`finalize`, on the
representation `Repr`), in terms of `Spec/Sha256.lean`, for any target:
`A` is the target's calling convention. The signatures fix where the
arguments are, the memory each function may access, disjointness, and that
the pointers and lengths are public (see `TCB/Sig.lean`); the contracts add
the postconditions and which other arguments are public. `update` and
`finalize` may overwrite their arguments passed in memory, where the calling
convention allows it (`writeArgs`), to pass arguments to the code they
inline.

`update` and `finalize` take the number of bytes of stack below the stack pointer that
an implementation's calls use (`stack`, see `Sig.contract`), 0 for one that
makes no call: it depends on the target, and on which functions the
implementation calls.
-/

namespace VG.Spec.Sha256

/-- `vg_sha256_compress(state: *mut [u32; 8], blocks: *const [u8; 64], n: usize, scratch: *mut [u64; 14])`.
`scratch` is working space. -/
def compressSig : Sig where
  params := [("state", .array true .u32 8), ("blocks", .slice false (.array .u8 64) "n"),
    ("scratch", .array true .u64 14)]

/-- Updates the hash value at `state` with the `n` 64-byte blocks at
`blocks`. The hash value and the blocks are secret. -/
def compressContract {M : ISA} (A : Abi M) : Contract M :=
  compressSig.contract A (post := fun state blocks n _scratch m m' _ =>
    stateAt m' state = compressBlocks (stateAt m state) m blocks n.toNat)

/-- `vg_sha256_compress` on every target. -/
def compressApi : Api where
  module := "sha256"
  name := "vg_sha256_compress"
  sig := compressSig
  summary := "The SHA-256 compression function (FIPS 180-4 §6.2.2): updates the hash value \
    `*state` with the `n` 64-byte blocks starting at `blocks`, in order.\n\n\
    Contract: `VG.Spec.Sha256.compressContract`. Constant time: only the pointers and `n` may \
    affect timing, not the hash value or the blocks."
  safety := [
    "`state` must be valid for reads and writes of 32 bytes.",
    "`blocks` must be valid for reads of `64 * n` bytes.",
    "`scratch` must be valid for reads and writes of 112 bytes; its contents on return are \
      unspecified."]

/-- `vg_sha256_init(state: *mut [u8; 96])`. -/
def initSig : Sig where
  params := [("state", .array true .u8 96)]

/-- Makes the streaming state at `state` represent the empty message. -/
def initContract {M : ISA} (A : Abi M) : Contract M :=
  initSig.contract A (post := fun state _ m' _ => Repr m' state [])

/-- `vg_sha256_init` on every target. -/
def initApi : Api where
  module := "sha256"
  name := "vg_sha256_init"
  sig := initSig
  summary := "Starts a SHA-256 computation: makes the streaming state `*state` represent the empty \
    message.\n\n\
    Contract: `VG.Spec.Sha256.initContract`. The streaming state is the hash value followed by a \
    buffered partial block (`VG.Spec.Sha256.Repr`)."
  safety := ["`state` must be valid for writes of 96 bytes."]

/-- `vg_sha256_update(state: *mut [u8; 96], count: u64, data: *const u8, len: usize, scratch: *mut [u64; 20])`.
`count` is public; `scratch` is working space. -/
def updateSig : Sig where
  params := [("state", .array true .u8 96), ("count", .int .u64 true),
    ("data", .slice false .u8 "len"), ("scratch", .array true .u64 20)]

/-- If the streaming state at `state` represents a message `msg` of `count`
bytes (modulo 2⁶⁴), then afterwards it represents `msg` followed by the `len`
bytes at `data`. The state and the data are secret. -/
def updateContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  updateSig.contract A (post := fun state count data len _scratch m m' _ =>
    ∀ msg, Repr m state msg → count = BitVec.ofNat 64 msg.length →
      Repr m' state (msg ++ bytesAt m data len.toNat))
    (writeArgs := true)
    (stack := stack)

/-- `vg_sha256_update` on every target. -/
def updateApi : Api where
  module := "sha256"
  name := "vg_sha256_update"
  sig := updateSig
  writeArgs := true
  summary := "Absorbs data into a SHA-256 computation: if the streaming state `*state` represents \
    a message of `count` bytes (modulo 2⁶⁴), it then represents that message followed by the `len` \
    bytes at `data`.\n\n\
    Contract: `VG.Spec.Sha256.updateContract`. Constant time: only the pointers, `count` and `len` \
    may affect timing, not the state or the data."
  safety := [
    "`state` must be valid for reads and writes of 96 bytes.",
    "`data` must be valid for reads of `len` bytes.",
    "`scratch` must be valid for reads and writes of 160 bytes; its contents on return are \
      unspecified."]

/-- `vg_sha256_finalize(state: *mut [u8; 96], count: u64, out: *mut [u8; 32], scratch: *mut [u64; 20])`.
`count` is public; `state` is left unspecified, and `scratch` is working
space. -/
def finalizeSig : Sig where
  params := [("state", .array true .u8 96), ("count", .int .u64 true),
    ("out", .array true .u8 32), ("scratch", .array true .u64 20)]

/-- If the streaming state at `state` represents a message `msg` of `count`
bytes (modulo 2⁶⁴), writes the SHA-256 digest of `msg` to `out`. The state is
secret. -/
def finalizeContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  finalizeSig.contract A (post := fun state count out _scratch m m' _ =>
    ∀ msg, Repr m state msg → count = BitVec.ofNat 64 msg.length → bytesAt m' out 32 = hash msg)
    (writeArgs := true)
    (stack := stack)

/-- `vg_sha256_finalize` on every target. -/
def finalizeApi : Api where
  module := "sha256"
  name := "vg_sha256_finalize"
  sig := finalizeSig
  writeArgs := true
  summary := "Finishes a SHA-256 computation: if the streaming state `*state` represents a message \
    of `count` bytes (modulo 2⁶⁴), writes the SHA-256 digest of that message to `*out`.\n\n\
    Contract: `VG.Spec.Sha256.finalizeContract`. Constant time: only the pointers and `count` may \
    affect timing, not the state."
  safety := [
    "`state` must be valid for reads and writes of 96 bytes; its contents on return are \
      unspecified.",
    "`out` must be valid for writes of 32 bytes.",
    "`scratch` must be valid for reads and writes of 160 bytes; its contents on return are \
      unspecified."]

end VG.Spec.Sha256
