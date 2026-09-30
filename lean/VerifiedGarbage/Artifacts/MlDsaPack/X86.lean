import VerifiedGarbage.TCB.X86.Target
import VerifiedGarbage.Proof.MlDsa.X86.Pack.Unpack

/-!
# ML-DSA (FIPS 204) on x86: the encodings

A registration file (see `TCB/Emit.lean`): the artifacts it lists are
emitted. **Review note**: `sig` and `doc` are trusted, as they tie the Rust
caller to the contract; check them against the contract's `pre`/`post`. An
artifact made from a function's `Api` (in `Spec/`, reviewed with the
contract) takes them from there, and this file adds only notes on the
implementation. The emitter adds the `# Safety` items that depend on the
target (`Sig.layoutDoc`), from `stack` and `writeArgs`, which `ofSig` checks
against the contract.

The functions call no other one, and save their caller's registers in a
frame of 16 bytes below the return address (`stack := 16`).
-/

namespace VG.Artifacts.MlDsaPack.X86

def artifacts : List Artifact := [
  { Spec.MlDsa.simpleBitPackApi with
    target := X86.target
    doc := Spec.MlDsa.simpleBitPackApi.doc
    code := Impl.MlDsa.X86.Pack.simpleBitPack
    contract := Spec.MlDsa.simpleBitPackContract X86.abi 16
    stack := 16
    verified := Proof.MlDsa.X86.Pack.SimpleBitPack.verified
    spSafe := Code.all_of_allInstrs (by decide +kernel) },
  { Spec.MlDsa.bitPackApi with
    target := X86.target
    doc := Spec.MlDsa.bitPackApi.doc
    code := Impl.MlDsa.X86.Pack.bitPack
    contract := Spec.MlDsa.bitPackContract X86.abi 16
    stack := 16
    verified := Proof.MlDsa.X86.Pack.BitPack.verified
    spSafe := Code.all_of_allInstrs (by decide +kernel) },
  { Spec.MlDsa.bitUnpackApi with
    target := X86.target
    doc := Spec.MlDsa.bitUnpackApi.doc
    code := Impl.MlDsa.X86.Pack.bitUnpack
    contract := Spec.MlDsa.bitUnpackContract X86.abi 16
    stack := 16
    verified := Proof.MlDsa.X86.Pack.Unpack.BU.verified
    spSafe := Code.all_of_allInstrs (by decide +kernel) },
  { Spec.MlDsa.unpackT1Api with
    target := X86.target
    doc := Spec.MlDsa.unpackT1Api.doc
    code := Impl.MlDsa.X86.Pack.unpackT1
    contract := Spec.MlDsa.unpackT1Contract X86.abi 16
    stack := 16
    verified := Proof.MlDsa.X86.Pack.Unpack.T1.verified
    spSafe := Code.all_of_allInstrs (by decide +kernel) }]

end VG.Artifacts.MlDsaPack.X86
