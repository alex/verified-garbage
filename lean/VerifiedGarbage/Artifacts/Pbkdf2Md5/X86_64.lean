import VerifiedGarbage.TCB.X86_64.Target
import VerifiedGarbage.Proof.Pbkdf2.X86_64.Instances

/-!
# The PBKDF2-HMAC-MD5 iteration (RFC 8018) on x86-64

A registration file (see `TCB/Emit.lean`): the artifacts it lists are
emitted. **Review note**: `sig` and `doc` are trusted, as they tie the Rust
caller to the contract; check them against the contract's `pre`/`post`. An
artifact made from a function's `Api` (in `Spec/`, reviewed with the
contract) takes them from there, and this file adds only notes on the
implementation. The emitter adds the `# Safety` items that depend on the
target (`Sig.layoutDoc`), from `stack` and `writeArgs`, which `ofSig` checks
against the contract (after unfolding the `Instance`'s contract to the
generic one, which is a `Sig.contract`).

The code is the one PBKDF2 iteration for every hash function whose streaming
code is the generic one (`Impl/Pbkdf2/X86_64.lean`), calling MD5's verified
compression function directly, twice per step.
-/

namespace VG.Artifacts.Pbkdf2Md5.X86_64

open VG.Impl.Pbkdf2.X86_64 (iterate)

def artifacts : List Artifact := [
  { Spec.Hmac.md5I.iterateApi with
    target := X86_64.target
    doc := Spec.Hmac.md5I.iterateApi.doc
    code := iterate Impl.Md5.X86_64.Stream.params 16 "vg_md5_compress" Impl.Md5.X86_64.compress
    contract := Spec.Hmac.md5I.iterateContract X86_64.abi 8
    ofSig := ⟨_, _, _, by unfold Spec.Hmac.Instance.iterateContract; rfl⟩
    writeArgs := true
    stack := 8
    verified := Proof.Pbkdf2.X86_64.Instances.md5
    spSafe := Code.all_of_allInstrs (by lit_decide) }]

end VG.Artifacts.Pbkdf2Md5.X86_64
