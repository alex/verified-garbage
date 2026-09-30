import VerifiedGarbage.TCB.X86_64.Target
import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.Variant

/-!
# PBKDF2-HMAC (RFC 8018) over a Merkle–Damgård hash function on x86-64

A generic file (see `TCB/Emit.lean`): PBKDF2's `iterate` (`Impl/Pbkdf2/X86_64.lean`)
and the whole `pbkdf2`, the one implementation for every Merkle–Damgård hash
function (`Impl/Pbkdf2/Md/X86_64.lean`), calling the variant's compression function
and the functions made with it, are emitted once for each variant
(`Variants/MdHash/X86_64/`), named with its suffix (e.g.
`vg_pbkdf2_hmac_sha256_shani`). **Review note**: `sig` and `doc` are
trusted, as they tie the Rust caller to the contract; check them against the
contract's `pre`/`post`. An artifact made from a function's `Api` (in
`Spec/`, reviewed with the contract) takes them from there. The emitter adds
the `# Safety` items that depend on the target (`Sig.layoutDoc`), from
`stack` and `writeArgs`, which `ofSig` checks against the contract (after
unfolding the `Instance`'s contract to the generic one, which is a
`Sig.contract`), and the CPU features the implementation needs.

`stack` is that of the shared contracts: 8 bytes for `iterate`, which calls
only the compression function, and 24 for `pbkdf2`, which calls HMAC's
functions, which call the streaming ones.
-/

namespace VG.Generic.MdHash.X86_64.Pbkdf2

def artifacts (v : Proof.Pbkdf2.Md.X86_64.MdHash) : List Artifact := [
  { v.I.iterateApi with
    name := v.I.iterateApi.name ++ v.suffix
    target := X86_64.target
    doc := v.I.iterateApi.doc
    code := v.H.iterate
    contract := v.I.iterateContract X86_64.abi 8
    ofSig := ⟨_, _, _, by unfold Spec.Hmac.Instance.iterateContract; rfl⟩
    writeArgs := true
    stack := 8
    verified := v.iterate
    spSafe := v.iterateSp
    features := v.features },
  { v.I.pbkdf2Api with
    name := v.I.pbkdf2Api.name ++ v.suffix
    target := X86_64.target
    doc := v.I.pbkdf2Api.doc
    code := v.H.pbkdf2
    contract := v.I.pbkdf2Contract X86_64.abi 24
    ofSig := ⟨_, _, _, by unfold Spec.Hmac.Instance.pbkdf2Contract; rfl⟩
    writeArgs := true
    stack := 24
    verified := v.pbkdf2
    spSafe := v.pbkdf2Sp
    features := v.features }]

end VG.Generic.MdHash.X86_64.Pbkdf2
