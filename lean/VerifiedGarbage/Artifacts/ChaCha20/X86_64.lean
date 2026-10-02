import VerifiedGarbage.TCB.X86_64.Target
import VerifiedGarbage.Proof.ChaCha20.X86_64.Xor
import VerifiedGarbage.Proof.ChaCha20.X86_64.Avx2.Xor
import VerifiedGarbage.Proof.ChaCha20.X86_64.Avx512.Xor
import VerifiedGarbage.Impl.ChaCha20.X86_64.Xor
import VerifiedGarbage.Impl.ChaCha20.X86_64.Avx2
import VerifiedGarbage.Impl.ChaCha20.X86_64.Avx512
import VerifiedGarbage.Proof.ChaCha20.X86_64.Lit
import VerifiedGarbage.Proof.ChaCha20.X86_64.Stream.Init

/-!
# The ChaCha20 block function (RFC 8439) on x86-64

A registration file (see `TCB/Emit.lean`): the artifacts it lists are
emitted. **Review note**: `sig` and `doc` are trusted, as they tie the Rust
caller to the contract; check them against the contract's `pre`/`post`. An
artifact made from a function's `Api` (in `Spec/`, reviewed with the
contract) takes them from there, and this file adds only notes on the
implementation. The emitter adds the `# Safety` items that depend on the
target (`Sig.layoutDoc`), from `stack` and `writeArgs`, which `ofSig` checks
against the contract.
-/

namespace VG.Artifacts.ChaCha20.X86_64

def artifacts : List Artifact := [
  { Spec.ChaCha20.blockApi with
    target := X86_64.target
    doc := Spec.ChaCha20.blockApi.doc
    code := Impl.ChaCha20.X86_64.block
    contract := Spec.ChaCha20.blockContract X86_64.abi
    verified := Proof.ChaCha20.X86_64.block_verified
    spSafe := Code.all_of_allInstrs (by lit_decide) },
  { Spec.ChaCha20.xorApi with
    target := X86_64.target
    doc := Spec.ChaCha20.xorApi.doc (notes := ["Calls `vg_chacha20_block` for each 64 bytes."])
    code := Impl.ChaCha20.X86_64.Xor.xor
    contract := Spec.ChaCha20.xorContract X86_64.abi 8
    stack := 8
    verified := Proof.ChaCha20.X86_64.Xor.xor_verified
    spSafe := Code.all_of_allInstrs (by lit_decide) },
  { Spec.ChaCha20.xorApi with
    name := "vg_chacha20_xor_avx2"
    target := X86_64.target
    doc := Spec.ChaCha20.xorApi.doc
      (notes := ["Uses AVX2: eight blocks at a time while at least 512 bytes remain, then \
        `vg_chacha20_xor` for the rest."])
    code := Impl.ChaCha20.X86_64.Avx2.xor
    contract := Spec.ChaCha20.xorContract X86_64.abi 16
    writeArgs := true
    stack := 16
    verified := Proof.ChaCha20.X86_64.Avx2.xor_verified
    features := ["avx", "avx2"]
    spSafe := Code.all_of_allInstrs (by lit_decide) },
  { Spec.ChaCha20.xorApi with
    name := "vg_chacha20_xor_avx512"
    target := X86_64.target
    doc := Spec.ChaCha20.xorApi.doc
      (notes := ["Uses AVX-512: sixteen blocks at a time while at least 1024 bytes remain, then \
        `vg_chacha20_xor` for the rest."])
    code := Impl.ChaCha20.X86_64.Avx512.xor
    contract := Spec.ChaCha20.xorContract X86_64.abi 16
    writeArgs := true
    stack := 16
    verified := Proof.ChaCha20.X86_64.Avx512.xor_verified
    features := ["avx", "avx512f"]
    spSafe := Code.all_of_allInstrs (by lit_decide) },
  { Spec.ChaCha20.initApi with
    target := X86_64.target
    doc := Spec.ChaCha20.initApi.doc
    code := Impl.ChaCha20.X86_64.Stream.init
    contract := Spec.ChaCha20.initContract X86_64.abi
    verified := Proof.ChaCha20.X86_64.Stream.init_verified
    spSafe := Code.all_of_allInstrs (by decide +kernel) },
  { Spec.ChaCha20.setNonceApi with
    target := X86_64.target
    doc := Spec.ChaCha20.setNonceApi.doc
    code := Impl.ChaCha20.X86_64.Stream.setNonce
    contract := Spec.ChaCha20.setNonceContract X86_64.abi
    verified := Proof.ChaCha20.X86_64.Stream.setNonce_verified
    spSafe := Code.all_of_allInstrs (by decide +kernel) }]

end VG.Artifacts.ChaCha20.X86_64
