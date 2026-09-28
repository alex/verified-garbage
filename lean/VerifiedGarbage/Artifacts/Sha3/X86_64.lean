import VerifiedGarbage.TCB.X86_64.Target
import VerifiedGarbage.Proof.Sha3.X86_64.Shared

/-!
# SHA-3 and SHAKE (FIPS 202) on x86-64

A registration file (see `TCB/Emit.lean`): the artifacts it lists are
emitted. **Review note**: `sig` and `doc` are trusted, as they tie the Rust
caller to the contract; check them against the contract's `pre`/`post`.
-/

namespace VG.Artifacts.Sha3.X86_64

def artifacts : List Artifact := [
  { target := X86_64.target
    module := "sha3"
    name := "vg_keccak_f1600"
    sig := Spec.Sha3.permuteSig
    doc := "The permutation Keccak-f[1600] (FIPS 202 §3.4): applies it to the state \
      `*state` (lane `x + 5y` at index `x + 5y`).\n\n\
      Contract: `VG.Spec.Sha3.permuteContract`. Constant time: only the pointers may affect \
      timing, not the state.\n\n\
      # Safety\n\n\
      * `state` must be valid for reads and writes of 200 bytes.\n\
      * `scratch` must be valid for reads and writes of 512 bytes; its contents on return \
      are unspecified.\n\
      * These two regions must not overlap each other, nor the return address on the stack \
      (distinct Rust objects never do)."
    code := Impl.Sha3.X86_64.permute
    contract := Spec.Sha3.permuteContract X86_64.abi
    verified := Proof.Sha3.X86_64.Shared.permute },
  { target := X86_64.target
    module := "sha3"
    name := "vg_keccak_absorb"
    sig := Spec.Sha3.absorbSig
    doc := "Absorbs data into a SHA-3 or SHAKE computation: if the state `*state` represents \
      a message whose length is `pos` modulo `rate` (`VG.Spec.Sha3.Repr`), it then represents \
      that message followed by the `len` bytes at `data`. Returns the position after them, \
      `(pos + len) % rate`.\n\n\
      Contract: `VG.Spec.Sha3.absorbContract`. Constant time: only the pointers, `rate`, `pos` \
      and `len` may affect timing, not the state or the data.\n\n\
      # Safety\n\n\
      * `rate` must be 72, 104, 136, 144 or 168, and `pos` less than `rate`.\n\
      * `state` must be valid for reads and writes of 200 bytes.\n\
      * `data` must be valid for reads of `len` bytes.\n\
      * `scratch` must be valid for reads and writes of 640 bytes; its contents on return \
      are unspecified.\n\
      * These three regions must not overlap each other, the return address on the stack, \
      or the 8 bytes of stack below it, where its call of `vg_keccak_f1600` stores its \
      return address (distinct Rust objects never do)."
    code := Impl.Sha3.X86_64.Stream.absorb
    contract := Spec.Sha3.absorbContract X86_64.abi 8
    verified := Proof.Sha3.X86_64.Shared.absorb },
  { target := X86_64.target
    module := "sha3"
    name := "vg_keccak_pad"
    sig := Spec.Sha3.padSig
    doc := "Pads a SHA-3 or SHAKE message: if the state `*state` represents a message whose \
      length is `pos` modulo `rate` (`VG.Spec.Sha3.Repr`), it becomes the state after \
      absorbing that message with the domain-separation suffix (the low byte of `suffix`, \
      with the first bit of the padding: `0x06` for SHA-3, `0x1f` for SHAKE) and \
      `pad10*1`.\n\n\
      Contract: `VG.Spec.Sha3.padContract`. Constant time: only the pointers, `rate`, `pos` \
      and `suffix` may affect timing, not the state.\n\n\
      # Safety\n\n\
      * `rate` must be 72, 104, 136, 144 or 168, and `pos` less than `rate`.\n\
      * `state` must be valid for reads and writes of 200 bytes.\n\
      * `scratch` must be valid for reads and writes of 640 bytes; its contents on return \
      are unspecified.\n\
      * These two regions must not overlap each other, the return address on the stack, \
      or the 8 bytes of stack below it, where its call of `vg_keccak_f1600` stores its \
      return address (distinct Rust objects never do)."
    code := Impl.Sha3.X86_64.Stream.pad
    contract := Spec.Sha3.padContract X86_64.abi 8
    verified := Proof.Sha3.X86_64.Shared.pad },
  { target := X86_64.target
    module := "sha3"
    name := "vg_keccak_squeeze"
    sig := Spec.Sha3.squeezeSig
    doc := "Squeezes output from a padded SHA-3 or SHAKE state: writes to `out` the \
      `outlen` bytes of the output of the sponge with rate `rate` from the state `*state` \
      (FIPS 202 Algorithm 8, steps 7 to 10), from byte `pos` of that output on; leaves in \
      `*state` a state, and returns a position, from which the output continues after them. \
      Start from the state `vg_keccak_pad` leaves and position 0.\n\n\
      Contract: `VG.Spec.Sha3.squeezeContract`. Constant time: only the pointers, `rate`, \
      `pos` and `outlen` may affect timing, not the state.\n\n\
      # Safety\n\n\
      * `rate` must be 72, 104, 136, 144 or 168, and `pos` at most `rate`.\n\
      * `state` must be valid for reads and writes of 200 bytes.\n\
      * `out` must be valid for writes of `outlen` bytes.\n\
      * `scratch` must be valid for reads and writes of 640 bytes; its contents on return \
      are unspecified.\n\
      * These three regions must not overlap each other, the return address on the stack, \
      or the 8 bytes of stack below it, where its call of `vg_keccak_f1600` stores its \
      return address (distinct Rust objects never do)."
    code := Impl.Sha3.X86_64.Stream.squeeze
    contract := Spec.Sha3.squeezeContract X86_64.abi 8
    verified := Proof.Sha3.X86_64.Shared.squeeze }]

end VG.Artifacts.Sha3.X86_64
