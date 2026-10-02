import VerifiedGarbage.TCB.X86_64.Target
import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.Variant

/-!
# HMAC (RFC 2104) over a Merkle–Damgård hash function on x86-64

A generic file (see `TCB/Emit.lean`): HMAC's `init` (for a key of any length) and `finalize`, the one
implementation for every Merkle–Damgård hash function
(`Impl/Hmac/Generic/X86_64.lean`), calling the hash function's streaming
functions made with the variant's compression function, are emitted once for
each variant (`Variants/MdHash/X86_64/`), named with its suffix (e.g.
`vg_hmac_sha256_init_shani`). **Review note**: `sig` and `doc` are
trusted, as they tie the Rust caller to the contract; check them against the
contract's `pre`/`post`. An artifact made from a function's `Api` (in
`Spec/`, reviewed with the contract) takes them from there. The emitter adds
the `# Safety` items that depend on the target (`Sig.layoutDoc`), from
`stack` and `writeArgs`, which `ofSig` checks against the contract (after
unfolding the `Instance`'s contract to the generic one, which is a
`Sig.contract`), and the CPU features the implementation needs.
-/

namespace VG.Generic.MdHash.X86_64.Hmac

def artifacts (v : Proof.Pbkdf2.Md.X86_64.MdHash) : List Artifact := [
  { v.I.initAnyKeyApi with
    name := v.I.initAnyKeyApi.name ++ v.suffix
    target := X86_64.target
    doc := v.I.initAnyKeyApi.doc
    code := v.H.hmacInit
    contract := v.I.initAnyKeyContract X86_64.abi 16
    ofSig := ⟨_, _, _, by unfold Spec.Hmac.Instance.initAnyKeyContract; rfl⟩
    stack := 16
    verified := v.hmacInit
    spSafe := v.hmacInitSp
    features := v.features },
  { v.I.finalizeApi with
    name := v.I.finalizeApi.name ++ v.suffix
    target := X86_64.target
    doc := v.I.finalizeApi.doc
    code := v.H.hmacFin
    contract := v.I.finalizeContract X86_64.abi 16
    ofSig := ⟨_, _, _, by unfold Spec.Hmac.Instance.finalizeContract; rfl⟩
    stack := 16
    verified := v.hmacFin
    spSafe := v.hmacFinSp
    features := v.features }]

end VG.Generic.MdHash.X86_64.Hmac
