import VerifiedGarbage.Spec.Sha3
import VerifiedGarbage.TCB.Artifact

/-!
# SHA-3 and SHAKE: the contracts, on every target

**Trusted** (as every file in `Spec/`). The contracts of the permutation
Keccak-f[1600] and of the streaming sponge (`absorb`/`pad`/`squeeze`, on the
representation `Repr`), in terms of `Spec/Sha3.lean`, for any target: `A` is
the target's calling convention. The signatures fix where the arguments are,
the memory each function may access, disjointness, and that the pointers and
lengths are public (see `TCB/Sig.lean`); the contracts add the
postconditions and which other arguments are public. The state and the
message are secret; the rate, the position within the block and the
domain-separation suffix are public.

A hash is computed from the all-zero state (which represents the empty
message) by `vg_keccak_absorb` on each piece of the message,
`vg_keccak_pad`, and `vg_keccak_squeeze` from position 0: by the
definitions, the output is then `sponge rate suffix msg outlen`. Further
calls of `vg_keccak_squeeze`, each from the state and position the previous
one left, output the bytes that follow (for SHAKE). SHA3-224/256/384/512 use the rates
144, 136, 104 and 72 and the suffix `sha3Suffix`; SHAKE128 and SHAKE256 the
rates 168 and 136 and the suffix `shakeSuffix`.

The streaming functions take the number of bytes of stack below the stack
pointer that an implementation's calls and frames use (`stack`, see
`Sig.contract`), 0 for one that uses none: it depends on the target. They
may overwrite their arguments passed in memory, where the calling
convention allows it (`writeArgs`). `scratch` is working space, sized for
the target with the fewest registers.
-/

namespace VG.Spec.Sha3

/-- The rates, in bytes, of the six functions of FIPS 202 (§6). -/
def rates : List Nat := [72, 104, 136, 144, 168]

/-- `vg_keccak_f1600(state: *mut [u64; 25], scratch: *mut [u64; 64])`.
`scratch` is working space. -/
def permuteSig : Sig where
  params := [("state", .array true .u64 25), ("scratch", .array true .u64 64)]

/-- Applies Keccak-f[1600] to the state at `state`. The state is secret. -/
def permuteContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  permuteSig.contract A (post := fun state _scratch m m' _ =>
    stateAt m' state = keccakF (stateAt m state))
    (stack := stack)

/-- `vg_keccak_f1600` on every target. -/
def permuteApi : Api where
  module := "sha3"
  name := "vg_keccak_f1600"
  sig := permuteSig
  summary := "The permutation Keccak-f[1600] (FIPS 202 §3.4): applies it to the state `*state` \
    (lane `x + 5y` at index `x + 5y`).\n\n\
    Contract: `VG.Spec.Sha3.permuteContract`. Constant time: only the pointers may affect timing, \
    not the state."
  safety := [
    "`state` must be valid for reads and writes of 200 bytes.",
    "`scratch` must be valid for reads and writes of 512 bytes; its contents on return are \
      unspecified."]

/-- `vg_keccak_absorb(state: *mut [u64; 25], rate: usize, pos: usize, data: *const u8, len: usize, scratch: *mut [u64; 80]) -> usize`.
`rate` and `pos` are public; `scratch` is working space. -/
def absorbSig : Sig where
  params := [("state", .array true .u64 25), ("rate", .int .usize true),
    ("pos", .int .usize true), ("data", .slice false .u8 "len"),
    ("scratch", .array true .u64 80)]
  ret := some .usize

/-- For a rate `rate` in `rates` and `pos < rate`: if the state at `state`
represents a message `msg` for `rate`, and `pos` is the length of `msg`
modulo `rate`, then afterwards it represents `msg` followed by the `len`
bytes at `data`. Returns `(pos + len) mod rate`, the position after them. -/
def absorbContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  absorbSig.contract A
    (pre := fun _state rate pos _data _len _scratch _ =>
      rate.toNat ∈ rates ∧ pos.toNat < rate.toNat)
    (post := fun state rate pos data len _scratch m m' ret =>
      (∀ msg, Repr m state rate.toNat msg → pos.toNat = msg.length % rate.toNat →
        Repr m' state rate.toNat (msg ++ bytesAt m data len.toNat)) ∧
      ret.toNat = (pos.toNat + len.toNat) % rate.toNat)
    (writeArgs := true)
    (stack := stack)

/-- `vg_keccak_absorb` on every target. -/
def absorbApi : Api where
  module := "sha3"
  name := "vg_keccak_absorb"
  sig := absorbSig
  writeArgs := true
  summary := "Absorbs data into a SHA-3 or SHAKE computation: if the state `*state` represents a \
    message whose length is `pos` modulo `rate` (`VG.Spec.Sha3.Repr`), it then represents that \
    message followed by the `len` bytes at `data`. Returns the position after them, \
    `(pos + len) % rate`.\n\n\
    Contract: `VG.Spec.Sha3.absorbContract`. Constant time: only the pointers, `rate`, `pos` and \
    `len` may affect timing, not the state or the data."
  safety := [
    "`rate` must be 72, 104, 136, 144 or 168, and `pos` less than `rate`.",
    "`state` must be valid for reads and writes of 200 bytes.",
    "`data` must be valid for reads of `len` bytes.",
    "`scratch` must be valid for reads and writes of 640 bytes; its contents on return are \
      unspecified."]

/-- `vg_keccak_pad(state: *mut [u64; 25], rate: usize, pos: usize, suffix: u32, scratch: *mut [u64; 80])`.
`rate`, `pos` and `suffix` are public; `scratch` is working space. -/
def padSig : Sig where
  params := [("state", .array true .u64 25), ("rate", .int .usize true),
    ("pos", .int .usize true), ("suffix", .int .u32 true), ("scratch", .array true .u64 80)]

/-- For a rate `rate` in `rates` and `pos < rate`: if the state at `state`
represents a message `msg` for `rate`, and `pos` is the length of `msg`
modulo `rate`, then afterwards it is the state after absorbing `msg`
padded with the domain-separation suffix `suffix` (its low byte) and
`pad10*1`. -/
def padContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  padSig.contract A
    (pre := fun _state rate pos _suffix _scratch _ =>
      rate.toNat ∈ rates ∧ pos.toNat < rate.toNat)
    (post := fun state rate pos suffix _scratch m m' _ =>
      ∀ msg, Repr m state rate.toNat msg → pos.toNat = msg.length % rate.toNat →
        stateAt m' state = absorb rate.toNat (pad rate.toNat (suffix.setWidth 8) msg))
    (writeArgs := true)
    (stack := stack)

/-- `vg_keccak_pad` on every target. -/
def padApi : Api where
  module := "sha3"
  name := "vg_keccak_pad"
  sig := padSig
  writeArgs := true
  summary := "Pads a SHA-3 or SHAKE message: if the state `*state` represents a message whose \
    length is `pos` modulo `rate` (`VG.Spec.Sha3.Repr`), it becomes the state after absorbing that \
    message with the domain-separation suffix (the low byte of `suffix`, with the first bit of the \
    padding: `0x06` for SHA-3, `0x1f` for SHAKE) and `pad10*1`.\n\n\
    Contract: `VG.Spec.Sha3.padContract`. Constant time: only the pointers, `rate`, `pos` and \
    `suffix` may affect timing, not the state."
  safety := [
    "`rate` must be 72, 104, 136, 144 or 168, and `pos` less than `rate`.",
    "`state` must be valid for reads and writes of 200 bytes.",
    "`scratch` must be valid for reads and writes of 640 bytes; its contents on return are \
      unspecified."]

/-- `vg_keccak_squeeze(state: *mut [u64; 25], rate: usize, pos: usize, out: *mut u8, outlen: usize, scratch: *mut [u64; 80]) -> usize`.
`rate` and `pos` are public; `scratch` is working space. -/
def squeezeSig : Sig where
  params := [("state", .array true .u64 25), ("rate", .int .usize true),
    ("pos", .int .usize true), ("out", .slice true .u8 "outlen"),
    ("scratch", .array true .u64 80)]
  ret := some .usize

/-- For a rate `rate` in `rates` and `pos ≤ rate`: writes to `out` the
`outlen` bytes of output (Algorithm 8, steps 7–10) from the state at `state`,
starting at byte `pos` of its output; and leaves a state and returns a
position from which the output continues after those bytes. So output can be
squeezed in pieces: from the state after `pad` and position 0, then from
each state and position a call leaves. -/
def squeezeContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  squeezeSig.contract A
    (pre := fun _state rate pos _out _outlen _scratch _ =>
      rate.toNat ∈ rates ∧ pos.toNat ≤ rate.toNat)
    (post := fun state rate pos out outlen _scratch m m' ret =>
      bytesAt m' out outlen.toNat = squeezeFrom rate.toNat (stateAt m state) pos.toNat outlen.toNat ∧
      ret.toNat ≤ rate.toNat ∧
      ∀ d, squeezeFrom rate.toNat (stateAt m' state) ret.toNat d =
        squeezeFrom rate.toNat (stateAt m state) (pos.toNat + outlen.toNat) d)
    (writeArgs := true)
    (stack := stack)

/-- `vg_keccak_squeeze` on every target. -/
def squeezeApi : Api where
  module := "sha3"
  name := "vg_keccak_squeeze"
  sig := squeezeSig
  writeArgs := true
  summary := "Squeezes output from a padded SHA-3 or SHAKE state: writes to `out` the `outlen` \
    bytes of the output of the sponge with rate `rate` from the state `*state` (FIPS 202 Algorithm \
    8, steps 7 to 10), from byte `pos` of that output on; leaves in `*state` a state, and returns \
    a position, from which the output continues after them. Start from the state `vg_keccak_pad` \
    leaves and position 0.\n\n\
    Contract: `VG.Spec.Sha3.squeezeContract`. Constant time: only the pointers, `rate`, `pos` and \
    `outlen` may affect timing, not the state."
  safety := [
    "`rate` must be 72, 104, 136, 144 or 168, and `pos` at most `rate`.",
    "`state` must be valid for reads and writes of 200 bytes.",
    "`out` must be valid for writes of `outlen` bytes.",
    "`scratch` must be valid for reads and writes of 640 bytes; its contents on return are \
      unspecified."]

end VG.Spec.Sha3
