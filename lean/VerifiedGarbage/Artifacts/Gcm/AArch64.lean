import VerifiedGarbage.TCB.AArch64.Target
import VerifiedGarbage.Proof.Gcm.AArch64.Shared

/-!
# GHASH on AArch64

A registration file (see `TCB/Emit.lean`): the artifacts it lists are
emitted. **Review note**: `sig` and `doc` are trusted, as they tie the Rust
caller to the contract; check them against the contract's `pre`/`post`.
-/

namespace VG.Artifacts.Gcm.AArch64

def artifacts : List Artifact := [
  { target := AArch64.target
    module := "gcm"
    name := "vg_ghash"
    sig := Spec.Gcm.ghashSig
    doc := "GHASH (NIST SP 800-38D §6.4) continued over whole blocks: with the hash subkey \
      `H` the block at `h`, replaces the block `Y` at `*y` with `Yₙ`, where `Y₀ = Y` and \
      `Yᵢ = (Yᵢ₋₁ ⊕ Xᵢ) • H` for the `n` 16-byte blocks `X₁ … Xₙ` starting at `data` (blocks \
      big-endian, `•` the multiplication of §6.3, computed bit by bit as its Algorithm 1 \
      does, with masks instead of branches).\n\n\
      Contract: `VG.Spec.Gcm.ghashContract`. Constant time: only the pointers and `n` may \
      affect timing, not `H`, `Y` or the data.\n\n\
      # Safety\n\n\
      * `h` must be valid for reads of 16 bytes.\n\
      * `y` must be valid for reads and writes of 16 bytes.\n\
      * `data` must be valid for reads of `16 * n` bytes.\n\
      * `scratch` must be valid for reads and writes of 256 bytes; its contents on return \
      are unspecified.\n\
      * `y` and `scratch` must not overlap each other, `h` or `data` (`h` and `data` may \
      overlap), and none of the four regions may wrap around the end of the address space \
      (distinct Rust objects never do)."
    code := Impl.Gcm.AArch64.ghash
    contract := Spec.Gcm.ghashContract AArch64.abi
    verified := Proof.Gcm.AArch64.Shared.ghash
    spSafe := Code.all_of_forall (fun _ => rfl) _ }]

end VG.Artifacts.Gcm.AArch64
