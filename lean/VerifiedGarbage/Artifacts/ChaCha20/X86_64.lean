import VerifiedGarbage.TCB.X86_64.Target
import VerifiedGarbage.Proof.ChaCha20.X86_64.Xor
import VerifiedGarbage.Proof.ChaCha20.X86_64.Avx2.Xor
import VerifiedGarbage.Proof.ChaCha20.X86_64.Avx512.Xor
import VerifiedGarbage.Impl.ChaCha20.X86_64.Xor
import VerifiedGarbage.Impl.ChaCha20.X86_64.Avx2
import VerifiedGarbage.Impl.ChaCha20.X86_64.Avx512
import VerifiedGarbage.Proof.ChaCha20.X86_64.Lit

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
    doc := Spec.ChaCha20.xorApi.doc
    code := Impl.ChaCha20.X86_64.Xor.xor
    contract := Spec.ChaCha20.xorContract X86_64.abi 8
    stack := 8
    verified := Proof.ChaCha20.X86_64.Xor.xor_verified
    spSafe := Code.all_of_allInstrs (by lit_decide) },
  { target := X86_64.target
    module := "chacha20"
    name := "vg_chacha20_xor_avx2"
    sig := Spec.ChaCha20.xorSig
    doc := "XORs the first `len` bytes of the ChaCha20 keystream of the 16-word state `*state` \
      (RFC 8439 §2.4: the block function of the state with its block counter, word 12, advanced \
      by 0, 1, … modulo 2³²) into the `len` bytes at `data`, with AVX2: eight blocks at a time \
      while at least 512 bytes remain, then `vg_chacha20_xor` for the rest.\n\n\
      Contract: `VG.Spec.ChaCha20.xorContract`. Constant time: only the pointers and `len` may \
      affect timing, not the state or the data.\n\n\
      # Safety\n\n\
      * The contents of `state` on return are unspecified.\n\
      * The contents of `buf` on return are unspecified."
    code := Impl.ChaCha20.X86_64.Avx2.xor
    contract := Spec.ChaCha20.xorContract X86_64.abi 16
    writeArgs := true
    stack := 16
    verified := Proof.ChaCha20.X86_64.Avx2.xor_verified
    features := ["avx", "avx2"]
    spSafe := Code.all_of_allInstrs (by lit_decide) },
  { target := X86_64.target
    module := "chacha20"
    name := "vg_chacha20_xor_avx512"
    sig := Spec.ChaCha20.xorSig
    doc := "XORs the first `len` bytes of the ChaCha20 keystream of the 16-word state `*state` \
      (RFC 8439 §2.4: the block function of the state with its block counter, word 12, advanced \
      by 0, 1, … modulo 2³²) into the `len` bytes at `data`, with AVX-512: sixteen blocks at a \
      time while at least 1024 bytes remain, then `vg_chacha20_xor` for the rest.\n\n\
      Contract: `VG.Spec.ChaCha20.xorContract`. Constant time: only the pointers and `len` may \
      affect timing, not the state or the data.\n\n\
      # Safety\n\n\
      * The contents of `state` on return are unspecified.\n\
      * The contents of `buf` on return are unspecified."
    code := Impl.ChaCha20.X86_64.Avx512.xor
    contract := Spec.ChaCha20.xorContract X86_64.abi 16
    writeArgs := true
    stack := 16
    verified := Proof.ChaCha20.X86_64.Avx512.xor_verified
    features := ["avx", "avx512f"]
    spSafe := Code.all_of_allInstrs (by lit_decide) }]

end VG.Artifacts.ChaCha20.X86_64
