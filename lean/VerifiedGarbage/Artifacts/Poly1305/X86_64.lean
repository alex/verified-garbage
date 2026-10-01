import VerifiedGarbage.TCB.X86_64.Target
import VerifiedGarbage.Impl.Poly1305.X86_64
import VerifiedGarbage.Proof.Poly1305.X86_64.Blocks
import VerifiedGarbage.Proof.Poly1305.X86_64.Finalize
import VerifiedGarbage.Proof.Poly1305.X86_64.Init
import VerifiedGarbage.Proof.Poly1305.X86_64.Lit
import VerifiedGarbage.Proof.Poly1305.X86_64.Avx2.Blocks
import VerifiedGarbage.Proof.Poly1305.X86_64.Avx512.Blocks

/-!
# Poly1305 (RFC 8439 §2.5) on x86-64

A registration file (see `TCB/Emit.lean`): the artifacts it lists are
emitted. **Review note**: `sig` and `doc` are trusted, as they tie the Rust
caller to the contract; check them against the contract's `pre`/`post`. An
artifact made from a function's `Api` (in `Spec/`, reviewed with the
contract) takes them from there, and this file adds only notes on the
implementation. The emitter adds the `# Safety` items that depend on the
target (`Sig.layoutDoc`), from `stack` and `writeArgs`, which `ofSig` checks
against the contract.

`vg_poly1305_update` calls an implementation of `vg_poly1305_blocks`, and is
in the generic file `Generic/Poly1305Blocks/X86_64/Poly1305.lean`, emitted
once for each.
-/

namespace VG.Artifacts.Poly1305.X86_64

def artifacts : List Artifact := [
  { Spec.Poly1305.initApi with
    target := X86_64.target
    doc := Spec.Poly1305.initApi.doc
    code := Impl.Poly1305.X86_64.init
    contract := Spec.Poly1305.initContract X86_64.abi
    verified := Proof.Poly1305.X86_64.init_verified
    spSafe := Code.all_of_allInstrs (by lit_decide) },
  { Spec.Poly1305.blocksApi with
    target := X86_64.target
    doc := Spec.Poly1305.blocksApi.doc
    code := Impl.Poly1305.X86_64.blocks
    contract := Spec.Poly1305.blocksContract X86_64.abi
    verified := Proof.Poly1305.X86_64.blocks_verified
    spSafe := Code.all_of_allInstrs (by lit_decide) },
  { Spec.Poly1305.blocksApi with
    name := Spec.Poly1305.blocksApi.name ++ "_avx2"
    target := X86_64.target
    doc := Spec.Poly1305.blocksApi.doc (notes := ["With AVX2: four blocks at a time, in four \
      interleaved Horner evaluations, once there are at least 16 blocks; fewer, and the last \
      `n mod 4`, with `vg_poly1305_blocks`. It sets MXCSR to Intel's value for data \
      operand-independent timing (`0x1FBF`) around its `vpmuludq`s, and restores it."])
    code := Impl.Poly1305.X86_64.Avx2.blocksAvx2
    contract := Spec.Poly1305.blocksContract X86_64.abi 8
    stack := 8
    verified := Proof.Poly1305.X86_64.Avx2.blocksAvx2_verified
    features := ["avx", "avx2"]
    spSafe := Code.all_of_allInstrs (by lit_decide) },
  { Spec.Poly1305.blocksApi with
    name := Spec.Poly1305.blocksApi.name ++ "_avx512"
    target := X86_64.target
    doc := Spec.Poly1305.blocksApi.doc (notes := ["With AVX-512F: eight blocks at a time, in eight \
      interleaved Horner evaluations in the quadwords of `zmm` registers, once there are at least 40 \
      blocks; fewer with `vg_poly1305_blocks_avx2`, and the last `n mod 8` with `vg_poly1305_blocks`. \
      It sets MXCSR to Intel's value for data operand-independent timing (`0x1FBF`) around its \
      `vpmuludq`s, and restores it."])
    code := Impl.Poly1305.X86_64.Avx512.blocksAvx512
    contract := Spec.Poly1305.blocksContract X86_64.abi 16
    stack := 16
    verified := Proof.Poly1305.X86_64.Avx512.blocksAvx512_verified
    features := ["avx", "avx512f", "avx2"]
    spSafe := Code.all_of_allInstrs (by lit_decide) },
  { Spec.Poly1305.finalizeApi with
    target := X86_64.target
    doc := Spec.Poly1305.finalizeApi.doc
    code := Impl.Poly1305.X86_64.finalize
    contract := Spec.Poly1305.finalizeContract X86_64.abi
    verified := Proof.Poly1305.X86_64.finalize_verified
    spSafe := Code.all_of_allInstrs (by lit_decide) }]

end VG.Artifacts.Poly1305.X86_64
