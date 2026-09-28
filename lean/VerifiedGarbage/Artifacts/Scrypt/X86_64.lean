import VerifiedGarbage.TCB.X86_64.Target
import VerifiedGarbage.Impl.Scrypt.X86_64.Salsa
import VerifiedGarbage.Impl.Scrypt.X86_64.BlockMix
import VerifiedGarbage.Impl.Scrypt.X86_64.RoMix
import VerifiedGarbage.Proof.Scrypt.X86_64.Shared

/-!
# scrypt (RFC 7914): Salsa20/8, scryptBlockMix and scryptROMix on x86-64

A registration file (see `TCB/Emit.lean`): the artifacts it lists are
emitted. **Review note**: `sig` and `doc` are trusted, as they tie the Rust
caller to the contract; check them against the contract's `pre`/`post`.
-/

namespace VG.Artifacts.Scrypt.X86_64

def artifacts : List Artifact := [
  { target := X86_64.target
    module := "scrypt"
    name := "vg_salsa20_8"
    sig := Spec.Scrypt.salsaSig
    doc := "The Salsa20/8 Core (RFC 7914 §3): replaces the 64 bytes `*b` by their Salsa20/8 \
      Core (the 16 little-endian words, 8 rounds, then the input added word by word).\n\n\
      Contract: `VG.Spec.Scrypt.salsaContract`. Constant time: only the pointers may affect \
      timing, not the data.\n\n\
      # Safety\n\n\
      * `b` must be valid for reads and writes of 64 bytes.\n\
      * `scratch` must be valid for reads and writes of 64 bytes. It is working space: its \
      contents on return are unspecified.\n\
      * `b` and `scratch` must not overlap each other, nor the return address on the stack, \
      and neither may wrap around the end of the address space (distinct Rust objects never do)."
    code := Impl.Scrypt.X86_64.salsa
    contract := Spec.Scrypt.salsaContract X86_64.abi
    verified := Proof.Scrypt.X86_64.Shared.salsa },
  { target := X86_64.target
    module := "scrypt"
    name := "vg_scrypt_blockmix"
    sig := Spec.Scrypt.blockMixSig
    doc := "scryptBlockMix (RFC 7914 §4) with block size parameter `r`: writes scryptBlockMix of \
      the `128 * r` bytes at `b` to the `128 * ry` bytes at `y`. Calls `vg_salsa20_8` for each \
      64-byte block.\n\n\
      Contract: `VG.Spec.Scrypt.blockMixContract`. Constant time: only the pointers and `r` may \
      affect timing, not the data.\n\n\
      # Safety\n\n\
      * `ry` must equal `r`, and `r` must be positive.\n\
      * `b` must be valid for reads of `128 * r` bytes, and `y` for reads and writes of \
      `128 * ry` bytes.\n\
      * `scratch` must be valid for reads and writes of 128 bytes. It is working space: its \
      contents on return are unspecified.\n\
      * `b`, `y` and `scratch` must not overlap each other, the return address on the stack, \
      or the 8 bytes of stack below it, where its calls of `vg_salsa20_8` store their return \
      address, and none may wrap around the end of the address space (distinct Rust objects \
      never do)."
    code := Impl.Scrypt.X86_64.blockMix
    contract := Spec.Scrypt.blockMixContract X86_64.abi 8
    verified := Proof.Scrypt.X86_64.Shared.blockMix },
  { target := X86_64.target
    module := "scrypt"
    name := "vg_scrypt_romix"
    sig := Spec.Scrypt.roMixSig
    doc := "scryptROMix (RFC 7914 §5) with block size parameter `r` and cost parameter \
      `N = vlen / r`: replaces the `128 * r` bytes at `b` by their scryptROMix. Step 2 writes \
      `V[0], …, V[N - 1]` to `v`. Calls `vg_scrypt_blockmix` for each scryptBlockMix.\n\n\
      Contract: `VG.Spec.Scrypt.roMixContract`. Not constant time in the indices: timing may \
      depend on the pointers, `r`, `N` and the indices `j` of step 3 \
      (`VG.Spec.Scrypt.roMixIndices`), which are derived from the data and so leak \
      information about it (as in every scrypt that indexes `V` directly), but on nothing \
      else.\n\n\
      # Safety\n\n\
      * `r` must be positive, `vlen` must be `N * r` for a power of two `N`, and `slen` must \
      be `r + 2`.\n\
      * `b` must be valid for reads and writes of `128 * r` bytes, `v` of `128 * vlen` bytes \
      and `scratch` of `128 * slen` bytes. `v` and `scratch` are working space: their \
      contents on return are unspecified.\n\
      * `b`, `v` and `scratch` must not overlap each other, the return address on the stack, \
      or the 16 bytes of stack below it, where its calls store their return addresses, and \
      none may wrap around the end of the address space (distinct Rust objects never do)."
    code := Impl.Scrypt.X86_64.roMix
    contract := Spec.Scrypt.roMixContract X86_64.abi 16
    verified := Proof.Scrypt.X86_64.Shared.roMix }]

end VG.Artifacts.Scrypt.X86_64
