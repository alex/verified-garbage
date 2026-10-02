import VerifiedGarbage.TCB.AArch64.Target
import VerifiedGarbage.Proof.Pbkdf2.Md.AArch64.Variant

/-!
# HMAC (RFC 2104) over a Merkle–Damgård hash function on AArch64

A generic file (see `TCB/Emit.lean`): HMAC's `init` and `finalize`, the one
implementation for every Merkle–Damgård hash function
(`Impl/Hmac/Generic/AArch64.lean`, `Impl/Pbkdf2/Md/AArch64.lean`), calling the
hash function's streaming functions, are emitted once for each variant
(`Variants/MdHash/AArch64/`), named with its suffix.

`stack` is the 16 bytes below the stack pointer that the streaming
functions may use for a frame saving `x30`.
-/

namespace VG.Generic.MdHash.AArch64.Hmac

def artifacts (v : Proof.Pbkdf2.Md.AArch64.MdHash) : List Artifact := [
  { v.I.initApi with
    name := v.I.initApi.name ++ v.suffix
    target := AArch64.target
    doc := v.I.initApi.doc
    code := v.H.hmacInit
    contract := v.I.initContract AArch64.abi 16
    ofSig := ⟨_, _, _, by unfold Spec.Hmac.Instance.initContract; rfl⟩
    stack := 16
    verified := v.hmacInit
    spSafe := Code.all_of_forall (fun _ => rfl) _
    features := v.features },
  { v.I.finalizeApi with
    name := v.I.finalizeApi.name ++ v.suffix
    target := AArch64.target
    doc := v.I.finalizeApi.doc
    code := v.H.hmacFin
    contract := v.I.finalizeContract AArch64.abi 16
    ofSig := ⟨_, _, _, by unfold Spec.Hmac.Instance.finalizeContract; rfl⟩
    stack := 16
    verified := v.hmacFin
    spSafe := Code.all_of_forall (fun _ => rfl) _
    features := v.features }]

end VG.Generic.MdHash.AArch64.Hmac
