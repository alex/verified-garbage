import VerifiedGarbage.TCB.X86_64.Target
import VerifiedGarbage.Proof.Aes.X86_64.Ctr32
import VerifiedGarbage.Proof.Aes.X86_64.ExpandKey
import VerifiedGarbage.Proof.Aes.X86_64.AesNi.Ctr32
import VerifiedGarbage.Proof.Aes.X86_64.AesNi.ExpandKey

/-!
# AES on x86-64

A registration file (see `TCB/Emit.lean`): the artifacts it lists are
emitted. **Review note**: `sig` and `doc` are trusted, as they tie the Rust
caller to the contract; check them against the contract's `pre`/`post`. An
artifact made from a function's `Api` (in `Spec/`, reviewed with the
contract) takes them from there, and this file adds only notes on the
implementation. The emitter adds the `# Safety` items that depend on the
target (`Sig.layoutDoc`), from `stack` and `writeArgs`, which `ofSig` checks
against the contract.
-/

namespace VG.Artifacts.Aes.X86_64

def artifacts : List Artifact := [
  { Spec.Aes.expandKeyApi with
    target := X86_64.target
    doc := Spec.Aes.expandKeyApi.doc
      (notes := ["`SUBWORD` uses a constant-time bitsliced S-box, in the style of BearSSL's \
        `aes_ct64` (Thomas Pornin, MIT licence)."])
    code := Impl.Aes.X86_64.expandKey
    contract := Spec.Aes.expandKeyContract X86_64.abi
    verified := Proof.Aes.X86_64.expandKey_verified
    spSafe := Code.all_of_allInstrs (by lit_decide) },
  { Spec.Gcm.ctr32Api with
    target := X86_64.target
    doc := Spec.Gcm.ctr32Api.doc
      (notes := ["Constant-time bitsliced AES, four blocks at a time, in the style of BearSSL's \
        `aes_ct64` (Thomas Pornin, MIT licence)."])
    code := Impl.Aes.X86_64.ctr32
    contract := Spec.Gcm.ctr32Contract X86_64.abi
    verified := Proof.Aes.X86_64.ctr32_verified
    spSafe := Code.all_of_allInstrs (by lit_decide) },
  { Spec.Aes.expandKeyApi with
    name := "vg_aes_expand_key_aesni"
    target := X86_64.target
    doc := "AES key expansion (FIPS 197 §5.2), with AES-NI: writes the key schedule of the \
      `key_len`-byte key at `key` (AES-128, AES-192 or AES-256) to the first `16 (Nr + 1)` bytes \
      of `schedule`, where `Nr = key_len / 4 + 6`: the words `w[0] … w[4 Nr + 3]` in order, each \
      as its 4 bytes. Four words at a time, with AESKEYGENASSIST.\n\n\
      Contract: `VG.Spec.Aes.expandKeyContract`. Constant time: only the pointers and `key_len` \
      may affect timing, not the key.\n\n\
      # Safety\n\n\
      * `key_len` must be 16, 24 or 32.\n\
      * The bytes of `schedule` after the first `16 (Nr + 1)` are unspecified on return.\n\
      * The contents of `scratch` on return are unspecified."
    code := Impl.Aes.X86_64.AesNi.expandKey
    contract := Spec.Aes.expandKeyContract X86_64.abi
    verified := Proof.Aes.X86_64.AesNi.Key.expandKey_verified
    features := ["aes"]
    spSafe := Code.all_of_allInstrs (by lit_decide) },
  { Spec.Gcm.ctr32Api with
    name := "vg_aes_ctr32_aesni"
    target := X86_64.target
    doc := "AES in GCM's counter mode (SP 800-38D §6.5, with `inc₃₂`), with AES-NI: XORs \
      `CIPH_K(CB₁) … CIPH_K(CBₙ)` into the `n` 16-byte blocks at `data`, where `CB₁` is the block \
      at `counter` and `CBᵢ₊₁ = inc₃₂(CBᵢ)`, and leaves `inc₃₂ⁿ(CB₁)` at `counter`. `CIPH_K` is \
      AES with `rounds` rounds and the key schedule in the first `16 (rounds + 1)` bytes of \
      `schedule` (as `vg_aes_expand_key_aesni` writes it). Eight blocks at a time, then one at \
      a time.\n\n\
      Contract: `VG.Spec.Gcm.ctr32Contract`. Constant time: only the pointers, `rounds` and \
      `n` may affect timing, not the key schedule, the counter block or the data.\n\n\
      # Safety\n\n\
      * `rounds` must be 10, 12 or 14.\n\
      * The contents of `scratch` on return are unspecified."
    code := Impl.Aes.X86_64.AesNi.ctr32
    contract := Spec.Gcm.ctr32Contract X86_64.abi
    verified := Proof.Aes.X86_64.AesNi.ctr32_verified
    features := ["aes", "ssse3"]
    spSafe := Code.all_of_allInstrs (by lit_decide) }]

end VG.Artifacts.Aes.X86_64
