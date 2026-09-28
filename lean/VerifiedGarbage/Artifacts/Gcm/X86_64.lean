import VerifiedGarbage.TCB.X86_64.Target
import VerifiedGarbage.Proof.Gcm.X86_64.Shared
import VerifiedGarbage.Proof.Gcm.X86_64.Pclmul.Shared

/-!
# GHASH on x86-64

A registration file (see `TCB/Emit.lean`): the artifacts it lists are
emitted. **Review note**: `sig` and `doc` are trusted, as they tie the Rust
caller to the contract; check them against the contract's `pre`/`post`.
-/

namespace VG.Artifacts.Gcm.X86_64

def artifacts : List Artifact := [
  { target := X86_64.target
    module := "gcm"
    name := "vg_ghash"
    sig := Spec.Gcm.ghashSig
    doc := "GHASH (NIST SP 800-38D §6.4) continued over whole blocks: with the hash subkey \
      `H` the block at `h`, replaces the block `Y` at `*y` with `Yₙ`, where `Y₀ = Y` and \
      `Yᵢ = (Yᵢ₋₁ ⊕ Xᵢ) • H` for the `n` 16-byte blocks `X₁ … Xₙ` starting at `data` (blocks \
      big-endian, `•` the multiplication of §6.3).\n\n\
      Contract: `VG.Spec.Gcm.ghashContract`. Constant time: only the pointers and `n` may \
      affect timing, not `H`, `Y` or the data.\n\n\
      # Safety\n\n\
      * `h` must be valid for reads of 16 bytes.\n\
      * `y` must be valid for reads and writes of 16 bytes.\n\
      * `data` must be valid for reads of `16 * n` bytes.\n\
      * `scratch` must be valid for reads and writes of 256 bytes; its contents on return \
      are unspecified.\n\
      * `y` and `scratch` must not overlap each other, `h` or `data` (`h` and `data` may \
      overlap). None of the four regions may overlap the return address on the stack or wrap \
      around the end of the address space (distinct Rust objects never do)."
    code := Impl.Gcm.X86_64.ghash
    contract := Spec.Gcm.ghashContract X86_64.abi
    verified := Proof.Gcm.X86_64.Shared.ghash },
  { target := X86_64.target
    module := "gcm"
    name := "vg_ghash_pclmul"
    sig := Spec.Gcm.ghashSig
    doc := "GHASH (SP 800-38D §6.4), with PCLMULQDQ: replaces the block `*y` with `GHASH_H` \
      continued from `*y` over the `n` 16-byte blocks starting at `data`, where `H` is the \
      hash subkey `*h` (`Y ← (Y ⊕ Xᵢ) • H` for each block `Xᵢ`, in order). Four blocks at a \
      time, with `H²`, `H³` and `H⁴` computed on each call.\n\n\
      Contract: `VG.Spec.Gcm.ghashContract`. Constant time: only the pointers and `n` may \
      affect timing, not `H`, `Y` or the data.\n\n\
      # Safety\n\n\
      * `h` must be valid for reads of 16 bytes.\n\
      * `y` must be valid for reads and writes of 16 bytes.\n\
      * `data` must be valid for reads of `16 * n` bytes.\n\
      * `scratch` must be valid for reads and writes of 256 bytes; its contents on return \
      are unspecified.\n\
      * `y` and `scratch` must not overlap each other, `h`, `data`, or the return address on \
      the stack (distinct Rust objects never do)."
    code := Impl.Gcm.X86_64.Pclmul.ghash
    contract := Spec.Gcm.ghashContract X86_64.abi
    verified := Proof.Gcm.X86_64.Pclmul.Shared.ghash
    features := ["pclmulqdq", "ssse3"] }]

end VG.Artifacts.Gcm.X86_64
