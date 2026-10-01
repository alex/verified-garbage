import VerifiedGarbage.Spec.Sha256
import VerifiedGarbage.TCB.Artifact

/-!
# SHA-256: the contracts, on every target

**Trusted** (as every file in `Spec/`). The contracts of the compression
function and of streaming SHA-224 and SHA-256 (`init`/`update`/`finalize`,
on the representation `ReprFrom`), in terms of `Spec/Sha256.lean`, for any
target:
`A` is the target's calling convention. The signatures fix where the
arguments are, the memory each function may access, disjointness, and that
the pointers and lengths are public (see `TCB/Sig.lean`); the contracts add
the postconditions and which other arguments are public. `update` and
`finalize` may overwrite their arguments passed in memory, where the calling
convention allows it (`writeArgs`), to pass arguments to the code they
inline.

SHA-224 and SHA-256 share `update` and `finalize`, which hold for a state
hashed from any initial hash value; each has its own `init`.

`update` and `finalize` take the number of bytes of stack below the stack pointer that
an implementation's calls use (`stack`, see `Sig.contract`), 0 for one that
makes no call: it depends on the target, and on which functions the
implementation calls.
-/

namespace VG.Spec.Sha256

/-- `vg_sha256_compress(state: *mut [u32; 8], blocks: *const [u8; 64], n: usize, scratch: *mut [u64; 70])`.
`scratch` is working space, sized for the tightest target: x86-64 with AVX2
keeps the message schedules of two blocks in it (512 bytes), and saves six
callee-saved registers. The other SHA-256 functions, and HMAC-SHA-256's and
PBKDF2-HMAC-SHA-256's, pass theirs to it, so theirs have room for it and for
what they keep across its calls. -/
def compressSig : Sig where
  params := [("state", .array true .u32 8), ("blocks", .slice false (.array .u8 64) "n"),
    ("scratch", .array true .u64 70)]

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
  contracts := some fun A _ => compressContract A
  summary := "The SHA-256 compression function (FIPS 180-4 §6.2.2): updates the hash value \
    `*state` with the `n` 64-byte blocks starting at `blocks`, in order.\n\n\
    Contract: `VG.Spec.Sha256.compressContract`. Constant time: only the pointers and `n` may \
    affect timing, not the hash value or the blocks."
  safety := ["The contents of `scratch` on return are unspecified."]

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
  contracts := some fun A _ => initContract A
  summary := "Starts a SHA-256 computation: makes the streaming state `*state` represent the empty \
    message.\n\n\
    Contract: `VG.Spec.Sha256.initContract`. The streaming state is the hash value followed by a \
    buffered partial block (`VG.Spec.Sha256.Repr`)."
  safety := []

/-- `vg_sha224_init(state: *mut [u8; 96])`, with `vg_sha256_init`'s signature
(`initSig`): makes the streaming state at `state` represent the empty message,
hashed from SHA-224's initial hash value `H0_224`. -/
def init224Contract {M : ISA} (A : Abi M) : Contract M :=
  initSig.contract A (post := fun state _ m' _ => ReprFrom H0_224 m' state [])

/-- `vg_sha224_init` on every target. -/
def init224Api : Api where
  module := "sha256"
  name := "vg_sha224_init"
  sig := initSig
  contracts := some fun A _ => init224Contract A
  summary := "Starts a SHA-224 computation: makes the SHA-256 streaming state `*state` represent \
    the empty message, hashed from the initial hash value of SHA-224 \
    (`VG.Spec.Sha256.H0_224`). Continue with `vg_sha256_update` and `vg_sha256_finalize`, and \
    take the first 28 bytes of the final hash value as the digest.\n\n\
    Contract: `VG.Spec.Sha256.init224Contract`. The streaming state is the hash value followed by \
    a buffered partial block (`VG.Spec.Sha256.ReprFrom`)."
  safety := []

/-- `vg_sha256_update(state: *mut [u8; 96], count: u64, data: *const u8, len: usize, scratch: *mut [u64; 76])`.
`count` is public; `scratch` is working space. -/
def updateSig : Sig where
  params := [("state", .array true .u8 96), ("count", .int .u64 true),
    ("data", .slice false .u8 "len"), ("scratch", .array true .u64 76)]

/-- If the streaming state at `state` represents a message `msg` of `count`
bytes (modulo 2⁶⁴), hashed from any initial hash value, then afterwards it
represents `msg` followed by the `len` bytes at `data`, from the same one.
The state and the data are secret. -/
def updateContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  updateSig.contract A (post := fun state count data len _scratch m m' _ =>
    ∀ iv msg, ReprFrom iv m state msg → count = BitVec.ofNat 64 msg.length →
      ReprFrom iv m' state (msg ++ bytesAt m data len.toNat))
    (writeArgs := true)
    (stack := stack)

/-- `vg_sha256_update` on every target. -/
def updateApi : Api where
  module := "sha256"
  name := "vg_sha256_update"
  sig := updateSig
  writeArgs := true
  contracts := some fun A stack => updateContract A stack
  summary := "Absorbs data into a SHA-224 or SHA-256 computation: if the streaming state `*state` \
    represents a message of `count` bytes (modulo 2⁶⁴), it then represents that message followed \
    by the `len` bytes at `data`.\n\n\
    Contract: `VG.Spec.Sha256.updateContract`. Constant time: only the pointers, `count` and `len` \
    may affect timing, not the state or the data."
  safety := ["The contents of `scratch` on return are unspecified."]

/-- `vg_sha256_finalize(state: *mut [u8; 96], count: u64, out: *mut [u8; 32], scratch: *mut [u64; 76])`.
`count` is public; `state` is left unspecified, and `scratch` is working
space. -/
def finalizeSig : Sig where
  params := [("state", .array true .u8 96), ("count", .int .u64 true),
    ("out", .array true .u8 32), ("scratch", .array true .u64 76)]

/-- If the streaming state at `state` represents a message `msg` of `count`
bytes (modulo 2⁶⁴), hashed from the initial hash value `iv`, writes the final
hash value `H⁽ᴺ⁾` of `msg` from `iv` (32 bytes; `finalHash iv msg`) to `out`:
the SHA-256 digest of `msg` if `iv` is `H0`, and the SHA-224 digest followed
by four more bytes if `iv` is `H0_224`. The state is secret. -/
def finalizeContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  finalizeSig.contract A (post := fun state count out _scratch m m' _ =>
    ∀ iv msg, ReprFrom iv m state msg → count = BitVec.ofNat 64 msg.length →
      bytesAt m' out 32 = finalHash iv msg)
    (writeArgs := true)
    (stack := stack)

/-- `vg_sha256_finalize` on every target. -/
def finalizeApi : Api where
  module := "sha256"
  name := "vg_sha256_finalize"
  sig := finalizeSig
  writeArgs := true
  contracts := some fun A stack => finalizeContract A stack
  summary := "Finishes a SHA-224 or SHA-256 computation: if the streaming state `*state` \
    represents a message of `count` bytes (modulo 2⁶⁴), hashed from an initial hash value, writes \
    the final hash value `H⁽ᴺ⁾` of that message (32 bytes) to `*out`. The SHA-256 digest is all of \
    it; the SHA-224 digest is its first 28 bytes.\n\n\
    Contract: `VG.Spec.Sha256.finalizeContract`. Constant time: only the pointers and `count` may \
    affect timing, not the state."
  safety := [
    "The contents of `state` on return are unspecified.",
    "The contents of `scratch` on return are unspecified."]

end VG.Spec.Sha256
