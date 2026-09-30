import VerifiedGarbage.TCB.AArch64.Target
import VerifiedGarbage.Proof.Gcm.AArch64.Ghash
import VerifiedGarbage.Proof.Gcm.AArch64.Pmull.Ghash

/-!
# GHASH on AArch64

A registration file (see `TCB/Emit.lean`): the artifacts it lists are
emitted. **Review note**: `sig` and `doc` are trusted, as they tie the Rust
caller to the contract; check them against the contract's `pre`/`post`. An
artifact made from a function's `Api` (in `Spec/`, reviewed with the
contract) takes them from there, and this file adds only notes on the
implementation. The emitter adds the `# Safety` items that depend on the
target (`Sig.layoutDoc`), from `stack` and `writeArgs`, which `ofSig` checks
against the contract.
-/

namespace VG.Artifacts.Gcm.AArch64

def artifacts : List Artifact := [
  { Spec.Gcm.ghashApi with
    target := AArch64.target
    doc := Spec.Gcm.ghashApi.doc
      (notes := ["`•` is computed bit by bit as Algorithm 1 of §6.3 does, with masks instead of \
        branches."])
    code := Impl.Gcm.AArch64.ghash
    contract := Spec.Gcm.ghashContract AArch64.abi
    verified := Proof.Gcm.AArch64.ghash_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { target := AArch64.target
    module := "gcm"
    name := "vg_ghash_pmull"
    sig := Spec.Gcm.ghashSig
    doc := "GHASH (SP 800-38D §6.4), with PMULL: replaces the block `*y` with `GHASH_H` \
      continued from `*y` over the `n` 16-byte blocks starting at `data`, where `H` is the \
      hash subkey `*h` (`Y ← (Y ⊕ Xᵢ) • H` for each block `Xᵢ`, in order). Eight blocks at a \
      time, with `H²` to `H⁸` computed on each call that has at least eight blocks.\n\n\
      Contract: `VG.Spec.Gcm.ghashContract`. Constant time: only the pointers and `n` may \
      affect timing, not `H`, `Y` or the data.\n\n\
      # Safety\n\n\
      * The contents of `scratch` on return are unspecified."
    code := Impl.Gcm.AArch64.Pmull.ghash
    contract := Spec.Gcm.ghashContract AArch64.abi
    verified := Proof.Gcm.AArch64.Pmull.ghash_verified
    features := ["aes"]
    spSafe := Code.all_of_forall (fun _ => rfl) _ }]

end VG.Artifacts.Gcm.AArch64
