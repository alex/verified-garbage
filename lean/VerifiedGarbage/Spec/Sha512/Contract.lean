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
-/

namespace VG.Spec.Sha512

/-- `vg_sha512_compress(state: *mut [u64; 8], blocks: *const [u8; 128], n: usize, scratch: *mut [u64; 22])`.
`scratch` is working space. -/
def compressSig : Sig where
  params := [("state", .array true .u64 8), ("blocks", .slice false (.array .u8 128) "n"),
    ("scratch", .array true .u64 22)]

/-- Updates the hash value at `state` with the `n` 128-byte blocks at
`blocks`. The hash value and the blocks are secret. -/
def compressContract {M : ISA} (A : Abi M) : Contract M :=
  compressSig.contract A (post := fun state blocks n _scratch m m' _ =>
    stateAt m' state = compressBlocks (stateAt m state) m blocks n.toNat)

/-- `vg_<alg>_init(state: *mut [u8; 192])`. -/
def initSig : Sig where
  params := [("state", .array true .u8 192)]

/-- Makes the streaming state at `state` represent the empty message, hashed
from `iv`, the initial hash value of `<alg>` (`H0_384`, `H0_512`,
`H0_512_224` or `H0_512_256`). -/
def initContract {M : ISA} (A : Abi M) (iv : HashValue) : Contract M :=
  initSig.contract A (post := fun state _ m' _ => Repr iv m' state [])

/-- `vg_sha512_update(state: *mut [u8; 192], count: u64, data: *const u8, len: usize, scratch: *mut [u64; 28])`.
`count` is public; `scratch` is working space. -/
def updateSig : Sig where
  params := [("state", .array true .u8 192), ("count", .int .u64 true),
    ("data", .slice false .u8 "len"), ("scratch", .array true .u64 28)]

/-- If the streaming state at `state` represents a message `msg` of `count`
bytes (modulo 2⁶⁴), hashed from any initial hash value, then afterwards it
represents `msg` followed by the `len` bytes at `data`, from the same one.
The state and the data are secret. -/
def updateContract {M : ISA} (A : Abi M) : Contract M :=
  updateSig.contract A (post := fun state count data len _scratch m m' _ =>
    ∀ iv msg, Repr iv m state msg → count = BitVec.ofNat 64 msg.length →
      Repr iv m' state (msg ++ bytesAt m data len.toNat))

/-- `vg_sha512_finalize(state: *mut [u8; 192], count: u64, out: *mut [u8; 64], scratch: *mut [u64; 28])`.
`count` is public; `state` is left unspecified, and `scratch` is working
space. -/
def finalizeSig : Sig where
  params := [("state", .array true .u8 192), ("count", .int .u64 true),
    ("out", .array true .u8 64), ("scratch", .array true .u64 28)]

/-- If the streaming state at `state` represents a message `msg` of `count`
bytes, fewer than 2⁶⁴, hashed from the initial hash value `iv`, writes the
final hash value `H⁽ᴺ⁾` of `msg` from `iv` (64 bytes; `finalHash iv msg`) to
`out`. The digest of SHA-384, SHA-512/224 or SHA-512/256 is its first 48,
28 or 32 bytes. The state is secret. -/
def finalizeContract {M : ISA} (A : Abi M) : Contract M :=
  finalizeSig.contract A (post := fun state count out _scratch m m' _ =>
    ∀ iv msg, Repr iv m state msg → msg.length < 2 ^ 64 → count = BitVec.ofNat 64 msg.length →
      bytesAt m' out 64 = finalHash iv msg)

end VG.Spec.Sha512
