import VerifiedGarbage.Spec.Md5
import VerifiedGarbage.TCB.Artifact

/-!
# MD5: the contracts, on every target

**Trusted** (as every file in `Spec/`). The contracts of the compression
function and of streaming MD5 (`init`/`update`/`finalize`, on the
representation `Repr`), in terms of `Spec/Md5.lean`, for any target:
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

namespace VG.Spec.Md5

/-- `vg_md5_compress(state: *mut [u32; 4], blocks: *const [u8; 64], n: usize, scratch: *mut [u64; 8])`.
`scratch` is working space. -/
def compressSig : Sig where
  params := [("state", .array true .u32 4), ("blocks", .slice false (.array .u8 64) "n"),
    ("scratch", .array true .u64 8)]

/-- Updates the MD buffer at `state` with the `n` 64-byte blocks at
`blocks`. The MD buffer and the blocks are secret. -/
def compressContract {M : ISA} (A : Abi M) : Contract M :=
  compressSig.contract A (post := fun state blocks n _scratch m m' _ =>
    stateAt m' state = compressBlocks (stateAt m state) m blocks n.toNat)

/-- `vg_md5_compress` on every target. -/
def compressApi : Api where
  module := "md5"
  name := "vg_md5_compress"
  sig := compressSig
  contracts := some fun A _ => compressContract A
  summary := "The MD5 compression function (RFC 1321 §3.4): updates the MD buffer `*state` \
    (`A, B, C, D`) with the `n` 64-byte blocks starting at `blocks`, in order.\n\n\
    Contract: `VG.Spec.Md5.compressContract`. Constant time: only the pointers and `n` may affect \
    timing, not the MD buffer or the blocks."
  safety := ["The contents of `scratch` on return are unspecified."]

/-- `vg_md5_init(state: *mut [u8; 80])`. -/
def initSig : Sig where
  params := [("state", .array true .u8 80)]

/-- Makes the streaming state at `state` represent the empty message. -/
def initContract {M : ISA} (A : Abi M) : Contract M :=
  initSig.contract A (post := fun state _ m' _ => Repr m' state [])

/-- `vg_md5_init` on every target. -/
def initApi : Api where
  module := "md5"
  name := "vg_md5_init"
  sig := initSig
  contracts := some fun A _ => initContract A
  summary := "Starts an MD5 computation: makes the streaming state `*state` represent the empty \
    message.\n\n\
    Contract: `VG.Spec.Md5.initContract`. The streaming state is the MD buffer followed by a \
    buffered partial block (`VG.Spec.Md5.Repr`)."
  safety := []

/-- `vg_md5_update(state: *mut [u8; 80], count: u64, data: *const u8, len: usize, scratch: *mut [u64; 14])`.
`count` is public; `scratch` is working space. -/
def updateSig : Sig where
  params := [("state", .array true .u8 80), ("count", .int .u64 true),
    ("data", .slice false .u8 "len"), ("scratch", .array true .u64 14)]

/-- If the streaming state at `state` represents a message `msg` of `count`
bytes (modulo 2⁶⁴), then afterwards it represents `msg` followed by the `len`
bytes at `data`. The state and the data are secret. -/
def updateContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  updateSig.contract A (post := fun state count data len _scratch m m' _ =>
    ∀ msg, Repr m state msg → count = BitVec.ofNat 64 msg.length →
      Repr m' state (msg ++ bytesAt m data len.toNat))
    (writeArgs := true)
    (stack := stack)

/-- `vg_md5_update` on every target. -/
def updateApi : Api where
  module := "md5"
  name := "vg_md5_update"
  sig := updateSig
  writeArgs := true
  contracts := some fun A stack => updateContract A stack
  summary := "Absorbs data into an MD5 computation: if the streaming state `*state` represents a \
    message of `count` bytes (modulo 2⁶⁴), it then represents that message followed by the `len` \
    bytes at `data`.\n\n\
    Contract: `VG.Spec.Md5.updateContract`. Constant time: only the pointers, `count` and `len` \
    may affect timing, not the state or the data."
  safety := ["The contents of `scratch` on return are unspecified."]

/-- `vg_md5_finalize(state: *mut [u8; 80], count: u64, out: *mut [u8; 16], scratch: *mut [u64; 14])`.
`count` is public; `state` is left unspecified, and `scratch` is working
space. -/
def finalizeSig : Sig where
  params := [("state", .array true .u8 80), ("count", .int .u64 true),
    ("out", .array true .u8 16), ("scratch", .array true .u64 14)]

/-- If the streaming state at `state` represents a message `msg` of `count`
bytes (modulo 2⁶⁴), writes the MD5 digest of `msg` to `out`. The state is
secret. -/
def finalizeContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  finalizeSig.contract A (post := fun state count out _scratch m m' _ =>
    ∀ msg, Repr m state msg → count = BitVec.ofNat 64 msg.length → bytesAt m' out 16 = hash msg)
    (writeArgs := true)
    (stack := stack)

/-- `vg_md5_finalize` on every target. -/
def finalizeApi : Api where
  module := "md5"
  name := "vg_md5_finalize"
  sig := finalizeSig
  writeArgs := true
  contracts := some fun A stack => finalizeContract A stack
  summary := "Finishes an MD5 computation: if the streaming state `*state` represents a message of \
    `count` bytes (modulo 2⁶⁴), writes the MD5 digest of that message to `*out`.\n\n\
    Contract: `VG.Spec.Md5.finalizeContract`. Constant time: only the pointers and `count` may \
    affect timing, not the state."
  safety := [
    "The contents of `state` on return are unspecified.",
    "The contents of `scratch` on return are unspecified."]

end VG.Spec.Md5
