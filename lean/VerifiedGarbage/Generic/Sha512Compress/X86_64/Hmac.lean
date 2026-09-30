import VerifiedGarbage.TCB.X86_64.Target
import VerifiedGarbage.Proof.Sha512.X86_64.Variant
import VerifiedGarbage.Proof.Hmac.Generic.X86_64.Instances

/-!
# HMAC-SHA-384, HMAC-SHA-512, HMAC-SHA-512/224 and HMAC-SHA-512/256 (RFC 2104) on x86-64

A generic file (see `TCB/Emit.lean`): the artifacts it lists, calling an
implementation `v` of the SHA-512 compression function (through the
streaming functions made with it, which `Sha512.lean` here emits named with
its suffix), are emitted once for each implementation
(`Variants/Sha512Compress/X86_64/`), named with its suffix (e.g.
`vg_hmac_sha384_init_avx2`), and need its CPU features. **Review note**:
`sig` and `doc` are trusted, as they tie the Rust caller to the contract;
check them against the contract's `pre`/`post`. An artifact made from a
function's `Api` (in `Spec/`, reviewed with the contract) takes them from
there, and this file adds only notes on the implementation. The emitter adds
the `# Safety` items that depend on the target (`Sig.layoutDoc`), from
`stack` and `writeArgs`, which `ofSig` checks against the contract (after
unfolding the `Instance`'s contract to the generic one, which is a
`Sig.contract`).

The code is the one HMAC implementation for every streaming hash function
(`Impl/Hmac/Generic/X86_64.lean`), calling each function's verified `init`,
and the family's `update` and `finalize`.
-/

namespace VG.Generic.Sha512Compress.X86_64.Hmac

open VG.Proof.Hmac.Generic.X86_64

def artifacts (v : Proof.Sha512.X86_64.Compress) : List Artifact := [
  { Spec.Hmac.sha384I.initApi with
    name := Spec.Hmac.sha384I.initApi.name ++ v.suffix
    target := X86_64.target
    doc := Spec.Hmac.sha384I.initApi.doc
    code := (sha384H v).init
    contract := Spec.Hmac.sha384I.initContract X86_64.abi 16
    ofSig := ⟨_, _, _, by unfold Spec.Hmac.Instance.initContract; rfl⟩
    writeArgs := true
    stack := 16
    verified := Instances.sha384_init v
    spSafe := Instances.sha384_initSp v
    features := v.features },
  { Spec.Hmac.sha384I.finalizeApi with
    name := Spec.Hmac.sha384I.finalizeApi.name ++ v.suffix
    target := X86_64.target
    doc := Spec.Hmac.sha384I.finalizeApi.doc
    code := (sha384H v).finalize
    contract := Spec.Hmac.sha384I.finalizeContract X86_64.abi 16
    ofSig := ⟨_, _, _, by unfold Spec.Hmac.Instance.finalizeContract; rfl⟩
    writeArgs := true
    stack := 16
    verified := Instances.sha384_finalize v
    spSafe := Instances.sha384_finSp v
    features := v.features },
  { Spec.Hmac.sha512I.initApi with
    name := Spec.Hmac.sha512I.initApi.name ++ v.suffix
    target := X86_64.target
    doc := Spec.Hmac.sha512I.initApi.doc
    code := (sha512H' v).init
    contract := Spec.Hmac.sha512I.initContract X86_64.abi 16
    ofSig := ⟨_, _, _, by unfold Spec.Hmac.Instance.initContract; rfl⟩
    writeArgs := true
    stack := 16
    verified := Instances.sha512_init v
    spSafe := Instances.sha512_initSp v
    features := v.features },
  { Spec.Hmac.sha512I.finalizeApi with
    name := Spec.Hmac.sha512I.finalizeApi.name ++ v.suffix
    target := X86_64.target
    doc := Spec.Hmac.sha512I.finalizeApi.doc
    code := (sha512H' v).finalize
    contract := Spec.Hmac.sha512I.finalizeContract X86_64.abi 16
    ofSig := ⟨_, _, _, by unfold Spec.Hmac.Instance.finalizeContract; rfl⟩
    writeArgs := true
    stack := 16
    verified := Instances.sha512_finalize v
    spSafe := Instances.sha512_finSp v
    features := v.features },
  { Spec.Hmac.sha512_224I.initApi with
    name := Spec.Hmac.sha512_224I.initApi.name ++ v.suffix
    target := X86_64.target
    doc := Spec.Hmac.sha512_224I.initApi.doc
    code := (sha512_224H v).init
    contract := Spec.Hmac.sha512_224I.initContract X86_64.abi 16
    ofSig := ⟨_, _, _, by unfold Spec.Hmac.Instance.initContract; rfl⟩
    writeArgs := true
    stack := 16
    verified := Instances.sha512_224_init v
    spSafe := Instances.sha512_224_initSp v
    features := v.features },
  { Spec.Hmac.sha512_224I.finalizeApi with
    name := Spec.Hmac.sha512_224I.finalizeApi.name ++ v.suffix
    target := X86_64.target
    doc := Spec.Hmac.sha512_224I.finalizeApi.doc
    code := (sha512_224H v).finalize
    contract := Spec.Hmac.sha512_224I.finalizeContract X86_64.abi 16
    ofSig := ⟨_, _, _, by unfold Spec.Hmac.Instance.finalizeContract; rfl⟩
    writeArgs := true
    stack := 16
    verified := Instances.sha512_224_finalize v
    spSafe := Instances.sha512_224_finSp v
    features := v.features },
  { Spec.Hmac.sha512_256I.initApi with
    name := Spec.Hmac.sha512_256I.initApi.name ++ v.suffix
    target := X86_64.target
    doc := Spec.Hmac.sha512_256I.initApi.doc
    code := (sha512_256H v).init
    contract := Spec.Hmac.sha512_256I.initContract X86_64.abi 16
    ofSig := ⟨_, _, _, by unfold Spec.Hmac.Instance.initContract; rfl⟩
    writeArgs := true
    stack := 16
    verified := Instances.sha512_256_init v
    spSafe := Instances.sha512_256_initSp v
    features := v.features },
  { Spec.Hmac.sha512_256I.finalizeApi with
    name := Spec.Hmac.sha512_256I.finalizeApi.name ++ v.suffix
    target := X86_64.target
    doc := Spec.Hmac.sha512_256I.finalizeApi.doc
    code := (sha512_256H v).finalize
    contract := Spec.Hmac.sha512_256I.finalizeContract X86_64.abi 16
    ofSig := ⟨_, _, _, by unfold Spec.Hmac.Instance.finalizeContract; rfl⟩
    writeArgs := true
    stack := 16
    verified := Instances.sha512_256_finalize v
    spSafe := Instances.sha512_256_finSp v
    features := v.features }]

end VG.Generic.Sha512Compress.X86_64.Hmac
