import VerifiedGarbage.TCB.X86_64.Target
import VerifiedGarbage.Proof.ChaCha20Poly1305.X86_64.Verified

/-!
# ChaCha20-Poly1305 (RFC 8439 §2.8) on x86-64

A generic file (see `TCB/Emit.lean`): the artifacts it lists, calling an
implementation `v` of `vg_chacha20_xor`, are emitted once for each
implementation (`Variants/ChaCha20Xor/X86_64/`), named with its suffix (e.g.
`vg_chacha20_poly1305_seal_avx2`), and need its CPU features. **Review
note**: `sig` and `doc` are trusted, as they tie the Rust caller to the
contract; check them against the contract's `pre`/`post`. An artifact made
from a function's `Api` (in `Spec/`, reviewed with the contract) takes them
from there, and this file adds only notes on the implementation. The emitter
adds the `# Safety` items that depend on the target (`Sig.layoutDoc`), from
`stack` and `writeArgs`, which `ofSig` checks against the contract.

The stack is 24 bytes for every implementation: the return address of the
call of `vg_chacha20_xor`, and up to 16 bytes for its own calls.
-/

namespace VG.Generic.ChaCha20Xor.X86_64.ChaCha20Poly1305

open VG.Proof.ChaCha20Poly1305.X86_64

/-- Which implementation of `vg_chacha20_xor` an instance calls. -/
def xorNote (v : Proof.ChaCha20.X86_64.XorImpl) : String :=
  "This implementation encrypts with `" ++ v.callee.name ++ "`."

def artifacts (v : Proof.ChaCha20.X86_64.XorImpl) : List Artifact := [
  { Spec.ChaCha20Poly1305.sealApi with
    name := Spec.ChaCha20Poly1305.sealApi.name ++ v.suffix
    target := X86_64.target
    doc := Spec.ChaCha20Poly1305.sealApi.doc (notes := [xorNote v])
    code := Impl.ChaCha20Poly1305.X86_64.«seal» v.callee
    contract := Spec.ChaCha20Poly1305.sealContract X86_64.abi 24
    stack := 24
    verified := seal_verified v
    spSafe := seal_spSafe v
    features := v.features },
  { Spec.ChaCha20Poly1305.openApi with
    name := Spec.ChaCha20Poly1305.openApi.name ++ v.suffix
    target := X86_64.target
    doc := Spec.ChaCha20Poly1305.openApi.doc (notes := [xorNote v])
    code := Impl.ChaCha20Poly1305.X86_64.«open» v.callee
    contract := Spec.ChaCha20Poly1305.openContract X86_64.abi 24
    stack := 24
    verified := open_verified v
    spSafe := open_spSafe v
    features := v.features }]

end VG.Generic.ChaCha20Xor.X86_64.ChaCha20Poly1305
