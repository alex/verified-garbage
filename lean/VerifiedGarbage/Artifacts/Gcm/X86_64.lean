import VerifiedGarbage.TCB.X86_64.Target
import VerifiedGarbage.Proof.Gcm.X86_64.Ghash
import VerifiedGarbage.Proof.Gcm.X86_64.Pclmul.Ghash

/-!
# GHASH on x86-64

A registration file (see `TCB/Emit.lean`): the artifacts it lists are
emitted. **Review note**: `sig` and `doc` are trusted, as they tie the Rust
caller to the contract; check them against the contract's `pre`/`post`. An
artifact made from a function's `Api` (in `Spec/`, reviewed with the
contract) takes them from there, and this file adds only notes on the
implementation. The emitter adds the `# Safety` items that depend on the
target (`Sig.layoutDoc`), from `stack` and `writeArgs`, which `ofSig` checks
against the contract.
-/

namespace VG.Artifacts.Gcm.X86_64

def artifacts : List Artifact := [
  { Spec.Gcm.ghashApi with
    target := X86_64.target
    doc := Spec.Gcm.ghashApi.doc
      (notes := ["The carry-less products are computed with integer multiplications (`mul`) of \
        operands with \"holes\" (every fourth bit), which keep the carries away from the bits of \
        the result, as in BearSSL's `ghash_ctmul64` (Thomas Pornin, MIT licence): three 64-bit \
        products per block (Karatsuba) by `x⁻¹ · H`, computed once, and a reduction by shifts \
        and XORs, in GCM's bit-reflected order."])
    code := Impl.Gcm.X86_64.ghash
    contract := Spec.Gcm.ghashContract X86_64.abi
    verified := Proof.Gcm.X86_64.ghash_verified
    spSafe := Code.all_of_allInstrs (by decide +kernel) },
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
      * The contents of `scratch` on return are unspecified."
    code := Impl.Gcm.X86_64.Pclmul.ghash
    contract := Spec.Gcm.ghashContract X86_64.abi
    verified := Proof.Gcm.X86_64.Pclmul.ghash_verified
    features := ["pclmulqdq", "ssse3"]
    spSafe := Code.all_of_allInstrs (by decide +kernel) }]

end VG.Artifacts.Gcm.X86_64
