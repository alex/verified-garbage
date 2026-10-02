import VerifiedGarbage.TCB.AArch64.Target
import VerifiedGarbage.Proof.Pbkdf2.Md.AArch64.Variant

/-!
# HMAC (RFC 2104) over a Merkle–Damgård hash function on AArch64

A generic file (see `TCB/Emit.lean`): HMAC's `init` and `finalize`, the one
implementation for every Merkle–Damgård hash function
(`Impl/Hmac/Generic/AArch64.lean`, `Impl/Pbkdf2/Md/AArch64.lean`), calling
the hash function's streaming functions, are emitted once for each variant
(`Variants/MdHash/AArch64/`), named with its suffix. **Review note**: `sig`
and `doc` are trusted, as they tie the Rust caller to the contract; check
them against the contract's `pre`/`post`. An artifact made from a function's
`Api` (in `Spec/`, reviewed with the contract) takes them from there. The
emitter adds the `# Safety` items that depend on the target
(`Sig.layoutDoc`), from `stack` and `writeArgs`, which `ofSig` checks
against the contract (after unfolding the `Instance`'s contract to the
generic one, which is a `Sig.contract`), and the CPU features the
implementation needs.

`stack` is the 16 bytes below the stack pointer that the streaming
functions may use for a frame saving `x30`.
-/

namespace VG.Generic.MdHash.AArch64.Hmac

def artifacts (v : Proof.Pbkdf2.Md.AArch64.MdHash) : List Artifact := [
  { v.I.initAnyKeyApi with
    name := v.I.initAnyKeyApi.name ++ v.suffix
    target := AArch64.target
    doc := v.I.initAnyKeyApi.doc
    code := v.H.hmacInit
    contract := v.I.initAnyKeyContract AArch64.abi 16
    ofSig := ⟨_, _, _, by unfold Spec.Hmac.Instance.initAnyKeyContract; rfl⟩
    writeArgs := true
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
    writeArgs := true
    stack := 16
    verified := v.hmacFin
    spSafe := Code.all_of_forall (fun _ => rfl) _
    features := v.features }]

end VG.Generic.MdHash.AArch64.Hmac
