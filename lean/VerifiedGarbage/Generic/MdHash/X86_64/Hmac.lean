import VerifiedGarbage.TCB.X86_64.Target
import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.Variant

/-!
# HMAC (RFC 2104) over a Merkle–Damgård hash function on x86-64

A generic file (see `TCB/Emit.lean`): HMAC's `init` and `finalize`, the one
implementation for every Merkle–Damgård hash function
(`Impl/Pbkdf2/Md/X86_64.lean`), calling the variant's compression function
(each once or twice), the hash function's streaming `init` and, in
`finalize`, its streaming `finalize` made with that compression function, are
emitted once for each variant (`Variants/MdHash/X86_64/`), named with its
suffix (e.g. `vg_hmac_sha256_init_shani`).
-/

namespace VG.Generic.MdHash.X86_64.Hmac

def artifacts (v : Proof.Pbkdf2.Md.X86_64.MdHash) : List Artifact := [
  { v.I.initApi with
    name := v.I.initApi.name ++ v.suffix
    target := X86_64.target
    doc := v.I.initApi.doc
    code := v.H.hmacInit
    contract := v.I.initContract X86_64.abi 16
    ofSig := ⟨_, _, _, by unfold Spec.Hmac.Instance.initContract; rfl⟩
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
