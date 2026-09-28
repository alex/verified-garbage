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
`vg_keccak_pad`, and `vg_keccak_squeeze`: by the definitions, the output is
then `sponge rate suffix msg outlen`. SHA3-224/256/384/512 use the rates
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

/-- `vg_keccak_squeeze(state: *mut [u64; 25], rate: usize, out: *mut u8, outlen: usize, scratch: *mut [u64; 80])`.
`rate` is public; `state` is left unspecified, and `scratch` is working
space. -/
def squeezeSig : Sig where
  params := [("state", .array true .u64 25), ("rate", .int .usize true),
    ("out", .slice true .u8 "outlen"), ("scratch", .array true .u64 80)]

/-- For a rate `rate` in `rates`: writes the first `outlen` bytes of the
output squeezed from the state at `state` (Algorithm 8, steps 7–10) to
`out`. -/
def squeezeContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  squeezeSig.contract A
    (pre := fun _state rate _out _outlen _scratch _ => rate.toNat ∈ rates)
    (post := fun state rate out outlen _scratch m m' _ =>
      bytesAt m' out outlen.toNat = squeeze rate.toNat (stateAt m state) outlen.toNat)
    (writeArgs := true)
    (stack := stack)

end VG.Spec.Sha3
