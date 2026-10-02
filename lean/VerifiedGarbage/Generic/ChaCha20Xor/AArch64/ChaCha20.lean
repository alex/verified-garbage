import VerifiedGarbage.Proof.ChaCha20.AArch64.XorVariant
import VerifiedGarbage.Proof.ChaCha20.AArch64.Stream.ApplyCT

/-!
# ChaCha20 (RFC 8439) on AArch64: `vg_chacha20_xor` and `vg_chacha20_apply`

A generic file (see `TCB/Emit.lean`): the artifacts it lists are emitted once
for each implementation `v` of `vg_chacha20_xor`
(`Variants/ChaCha20Xor/AArch64/`), named with its suffix (e.g.
`vg_chacha20_apply_neon`): the implementation itself, and `apply`, which
calls it for the whole blocks. **Review note**: `sig` and `doc` are trusted,
as they tie the Rust caller to the contract; check them against the
contract's `pre`/`post`. An artifact made from a function's `Api` (in
`Spec/`, reviewed with the contract) takes them from there, and this file
adds only notes on the implementation. The emitter adds the `# Safety` items
that depend on the target (`Sig.layoutDoc`), from `stack` and `writeArgs`,
which `ofSig` checks against the contract.
-/

namespace VG.Generic.ChaCha20Xor.AArch64.ChaCha20

def artifacts (v : Proof.ChaCha20.AArch64.XorImpl) : List Artifact := [
  { Spec.ChaCha20.xorApi with
    name := Spec.ChaCha20.xorApi.name ++ v.callee.suffix
    target := AArch64.target
    doc := Spec.ChaCha20.xorApi.doc (notes := ["Stream backend `" ++ v.callee.name ++ "`."])
    code := v.callee.code
    contract := Spec.ChaCha20.xorContract AArch64.abi
    verified := v.verified
    features := v.features
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.ChaCha20.applyApi with
    name := Spec.ChaCha20.applyApi.name ++ v.callee.suffix
    target := AArch64.target
    doc := Spec.ChaCha20.applyApi.doc (notes := ["This implementation XORs the whole blocks with `" ++
      v.callee.name ++ "`."])
    code := Impl.ChaCha20.AArch64.Stream.apply v.callee
    contract := Spec.ChaCha20.applyContract AArch64.abi 0
    verified := Proof.ChaCha20.AArch64.Stream.apply_verified v
    features := v.features
    spSafe := Code.all_of_forall (fun _ => rfl) _ }]

end VG.Generic.ChaCha20Xor.AArch64.ChaCha20
