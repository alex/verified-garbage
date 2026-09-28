import VerifiedGarbage.TCB.X86_64.Target
import VerifiedGarbage.Proof.Aes.X86_64.Shared

/-!
# AES on x86-64

A registration file (see `TCB/Emit.lean`): the artifacts it lists are
emitted. **Review note**: `sig` and `doc` are trusted, as they tie the Rust
caller to the contract; check them against the contract's `pre`/`post`.
-/

namespace VG.Artifacts.Aes.X86_64

def artifacts : List Artifact := [
  { target := X86_64.target
    module := "aes"
    name := "vg_aes_expand_key"
    sig := Spec.Aes.expandKeySig
    doc := "The AES key expansion (FIPS 197 §5.2, `KEYEXPANSION`): writes the key schedule of the \
      `key_len`-byte key at `key`, the words `w[0] … w[4 * Nr + 3]` for `Nr = key_len / 4 + 6` \
      rounds, each as its 4 bytes (`16 * (Nr + 1)` bytes in all), to the start of `*schedule`, \
      as `vg_aes_ctr32` reads it. `SUBWORD` uses a constant-time bitsliced S-box, in the style of \
      BearSSL's `aes_ct64` (Thomas Pornin, MIT licence).\n\n\
      Contract: `VG.Spec.Aes.expandKeyContract`. Constant time: only the pointers and `key_len` \
      may affect timing, not the key.\n\n\
      # Safety\n\n\
      * `key_len` must be 16, 24 or 32.\n\
      * `key` must be valid for reads of `key_len` bytes.\n\
      * `schedule` must be valid for reads and writes of 240 bytes; its bytes after the key \
      schedule are unspecified on return.\n\
      * `scratch` must be valid for reads and writes of 512 bytes; its contents on return \
      are unspecified.\n\
      * `key`, `schedule` and `scratch` must not overlap each other, `schedule` and `scratch` \
      must not overlap the return address on the stack, and no region may wrap around the end \
      of the address space (distinct Rust objects never do)."
    code := Impl.Aes.X86_64.expandKey
    contract := Spec.Aes.expandKeyContract X86_64.abi
    verified := Proof.Aes.X86_64.Shared.expandKey },
  { target := X86_64.target
    module := "aes"
    name := "vg_aes_ctr32"
    sig := Spec.Gcm.ctr32Sig
    doc := "AES counter mode with GCM's 32-bit increment (NIST SP 800-38D §6.5, on whole \
      blocks): XORs `CIPH_K(CB₁) … CIPH_K(CBₙ)` into the `n` 16-byte blocks at `data`, where \
      `CB₁` is the counter block `*counter` and `CBᵢ₊₁ = inc₃₂(CBᵢ)`, and leaves \
      `inc₃₂ⁿ(CB₁)` in `*counter`. `CIPH_K` is AES (FIPS 197) with `rounds` rounds and the key \
      schedule in the first `16 * (rounds + 1)` bytes of `*schedule`, as `vg_aes_expand_key` \
      writes it. Constant-time bitsliced AES, four blocks at a time, in the style of BearSSL's \
      `aes_ct64` (Thomas Pornin, MIT licence).\n\n\
      Contract: `VG.Spec.Gcm.ctr32Contract`. Constant time: only the pointers, `rounds` and \
      `n` may affect timing, not the key schedule, the counter block or the data.\n\n\
      # Safety\n\n\
      * `rounds` must be 10, 12 or 14.\n\
      * `schedule` must be valid for reads of 240 bytes.\n\
      * `counter` must be valid for reads and writes of 16 bytes.\n\
      * `data` must be valid for reads and writes of `16 * n` bytes.\n\
      * `scratch` must be valid for reads and writes of 2048 bytes; its contents on return \
      are unspecified.\n\
      * `counter`, `data` and `scratch` must not overlap each other, `schedule`, or the \
      return address on the stack, and no region may wrap around the end of the address \
      space (distinct Rust objects never do)."
    code := Impl.Aes.X86_64.ctr32
    contract := Spec.Gcm.ctr32Contract X86_64.abi
    verified := Proof.Aes.X86_64.Shared.ctr32 }]

end VG.Artifacts.Aes.X86_64
