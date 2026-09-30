import VerifiedGarbage.TCB.AArch64.Target
import VerifiedGarbage.Proof.Pbkdf2.Md.AArch64.Variant

/-!
# PBKDF2-HMAC (RFC 8018) over a Merkle–Damgård hash function on AArch64

A generic file (see `TCB/Emit.lean`): PBKDF2's `iterate` (`Impl/Pbkdf2/AArch64.lean`)
and the whole `pbkdf2`, the one implementation for every Merkle–Damgård hash
function (`Impl/Pbkdf2/Md/AArch64.lean`), calling the variant's compression
function and the functions made with it, are emitted once for each variant
(`Variants/MdHash/AArch64/`), named with its suffix. **Review note**: `sig`
and `doc` are trusted, as they tie the Rust caller to the contract; check
them against the contract's `pre`/`post`. An artifact made from a function's
`Api` (in `Spec/`, reviewed with the contract) takes them from there. The
emitter adds the `# Safety` items that depend on the target
(`Sig.layoutDoc`), from `stack` and `writeArgs`, which `ofSig` checks
against the contract (after unfolding the `Instance`'s contract to the
generic one, which is a `Sig.contract`), and the CPU features the
implementation needs.

`stack` is that of the shared contracts: none for `iterate`, which calls
only the compression function (which pushes no frame), and 16 bytes for
`pbkdf2`, whose callees' callees (the streaming functions) may push a frame
saving `x30`. Neither function pushes a frame of its own: each saves its
return address in `scratch`.
-/

namespace VG.Generic.MdHash.AArch64.Pbkdf2

def artifacts (v : Proof.Pbkdf2.Md.AArch64.MdHash) : List Artifact := [
  { v.I.iterateApi with
    name := v.I.iterateApi.name ++ v.suffix
    target := AArch64.target
    doc := v.I.iterateApi.doc
      (notes := ["The function uses no stack: it saves its return address in `scratch`."])
    code := v.H.iterate
    contract := v.I.iterateContract AArch64.abi
    ofSig := ⟨_, _, _, by unfold Spec.Hmac.Instance.iterateContract; rfl⟩
    writeArgs := true
    verified := v.iterate
    spSafe := Code.all_of_forall (fun _ => rfl) _
    features := v.features },
  { v.I.pbkdf2Api with
    name := v.I.pbkdf2Api.name ++ v.suffix
    target := AArch64.target
    doc := v.I.pbkdf2Api.doc
    code := v.H.pbkdf2
    contract := v.I.pbkdf2Contract AArch64.abi 16
    ofSig := ⟨_, _, _, by unfold Spec.Hmac.Instance.pbkdf2Contract; rfl⟩
    writeArgs := true
    stack := 16
    verified := v.pbkdf2
    spSafe := Code.all_of_forall (fun _ => rfl) _
    features := v.features }]

end VG.Generic.MdHash.AArch64.Pbkdf2
