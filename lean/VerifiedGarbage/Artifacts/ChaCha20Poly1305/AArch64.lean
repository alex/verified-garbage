import VerifiedGarbage.TCB.AArch64.Target
import VerifiedGarbage.Impl.ChaCha20Poly1305.AArch64
import VerifiedGarbage.Proof.ChaCha20Poly1305.AArch64.Shared

/-!
# ChaCha20-Poly1305 (RFC 8439 §2.8) on AArch64

A registration file (see `TCB/Emit.lean`): the artifacts it lists are
emitted. **Review note**: `sig` and `doc` are trusted, as they tie the Rust
caller to the contract; check them against the contract's `pre`/`post`.
-/

namespace VG.Artifacts.ChaCha20Poly1305.AArch64

def artifacts : List Artifact := [
  { target := AArch64.target
    module := "chacha20poly1305"
    name := "vg_chacha20_poly1305_seal"
    sig := Spec.ChaCha20Poly1305.sealSig
    doc := "ChaCha20-Poly1305 encryption (RFC 8439 §2.8): with the key in bytes 0–31 of \
      `*ctx` and the nonce in bytes 32–43, encrypts the `len` bytes at `data` in place and \
      writes the tag of the ciphertext and the `aad_len` bytes of additional data at `aad` \
      to bytes 48–63 of `*ctx`. The rest of `*ctx` is working space, unspecified on return. \
      Composed of calls of `vg_chacha20_block`, `vg_chacha20_xor` and the Poly1305 \
      functions.\n\n\
      Contract: `VG.Spec.ChaCha20Poly1305.sealContract`. Constant time: only the pointers \
      and the lengths may affect timing, not the key, the nonce or the data. The block \
      counter wraps around beyond 2³²-1 blocks of data (RFC 8439's `P_MAX`), which the \
      caller must not exceed for the construction to be secure.\n\n\
      # Safety\n\n\
      * `ctx` must be valid for reads and writes of 1024 bytes.\n\
      * `aad` must be valid for reads of `aad_len` bytes.\n\
      * `data` must be valid for reads and writes of `len` bytes.\n\
      * `ctx` and `data` must not overlap each other or `aad`, and none of them may wrap \
      around the end of the address space (distinct Rust objects never do)."
    code := Impl.ChaCha20Poly1305.AArch64.«seal»
    contract := Spec.ChaCha20Poly1305.sealContract AArch64.abi
    verified := Proof.ChaCha20Poly1305.AArch64.Shared.«seal»
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { target := AArch64.target
    module := "chacha20poly1305"
    name := "vg_chacha20_poly1305_open"
    sig := Spec.ChaCha20Poly1305.openSig
    doc := "ChaCha20-Poly1305 decryption (RFC 8439 §2.8): with the key in bytes 0–31 of \
      `*ctx`, the nonce in bytes 32–43 and the received tag in bytes 48–63, returns 1 if \
      the tag is that of the `len` bytes of ciphertext at `data` and the `aad_len` bytes of \
      additional data at `aad`, having decrypted the ciphertext in place; otherwise returns \
      0, and the bytes at `data` are unspecified (they must not be used). The rest of \
      `*ctx` is working space, unspecified on return. The tags are compared without a \
      branch.\n\n\
      Contract: `VG.Spec.ChaCha20Poly1305.openContract`. Constant time: only the pointers \
      and the lengths may affect timing, not the key, the nonce, the tag or the data.\n\n\
      # Safety\n\n\
      * `ctx` must be valid for reads and writes of 1024 bytes.\n\
      * `aad` must be valid for reads of `aad_len` bytes.\n\
      * `data` must be valid for reads and writes of `len` bytes.\n\
      * `ctx` and `data` must not overlap each other or `aad`, and none of them may wrap \
      around the end of the address space (distinct Rust objects never do)."
    code := Impl.ChaCha20Poly1305.AArch64.«open»
    contract := Spec.ChaCha20Poly1305.openContract AArch64.abi
    verified := Proof.ChaCha20Poly1305.AArch64.Shared.«open»
    spSafe := Code.all_of_forall (fun _ => rfl) _ }]

end VG.Artifacts.ChaCha20Poly1305.AArch64
