import VerifiedGarbage.TCB.X86.Target
import VerifiedGarbage.Proof.Gcm.X86.Ghash
import VerifiedGarbage.Proof.Gcm.X86.Pclmul.Ghash

/-!
# GHASH on x86

A registration file (see `TCB/Emit.lean`): the artifacts it lists are
emitted. **Review note**: `sig` and `doc` are trusted, as they tie the Rust
caller to the contract; check them against the contract's `pre`/`post`. An
artifact made from a function's `Api` (in `Spec/`, reviewed with the
contract) takes them from there, and this file adds only notes on the
implementation. The emitter adds the `# Safety` items that depend on the
target (`Sig.layoutDoc`), from `stack` and `writeArgs`, which `ofSig` checks
against the contract.
-/

namespace VG.Artifacts.Gcm.X86

def artifacts : List Artifact := [
  { Spec.Gcm.ghashApi with
    target := X86.target
    doc := Spec.Gcm.ghashApi.doc
      (notes := ["`•` is computed bit by bit as Algorithm 1 of §6.3 does, with masks instead of \
        branches."])
    code := Impl.Gcm.X86.ghash
    contract := Spec.Gcm.ghashContract X86.abi
    verified := Proof.Gcm.X86.ghash_verified
    spSafe := Code.all_of_allInstrs (by lit_decide) },
  { Spec.Gcm.ghashApi with
    target := X86.target
    name := "vg_ghash_pclmul"
    features := ["pclmulqdq", "ssse3"]
    doc := Spec.Gcm.ghashApi.doc
      (notes := ["PCLMULQDQ multiplication with SSSE3 byte reversal, processing one block at a time. \
        The implementation retains the accumulator and transformed hash key in SSE registers and \
        does not use the scratch buffer."])
    code := Impl.Gcm.X86.Pclmul.ghash
    contract := Spec.Gcm.ghashContract X86.abi
    stack := 0
    verified := Proof.Gcm.X86.Pclmul.ghash_verified
    spSafe := Code.all_of_allInstrs (by lit_decide) }]

end VG.Artifacts.Gcm.X86
