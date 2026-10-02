import VerifiedGarbage.TCB.X86_64.Target
import VerifiedGarbage.Proof.Poly1305.X86_64.UpdateVerified

/-!
# Streaming Poly1305 (RFC 8439 §2.5) on x86-64

A generic file (see `TCB/Emit.lean`): the artifacts it lists, which absorb the
whole blocks of the data with an implementation `v` of `vg_poly1305_blocks`,
are emitted once for each implementation (`Variants/Poly1305Blocks/X86_64/`),
named with its suffix (e.g. `vg_poly1305_update_avx2`), and need its CPU
features. `init` and `finalize` call no implementation of it, and are in the
registration file.

The stack is 24 bytes for every implementation: the return address of the
call of `vg_poly1305_blocks`, and up to 16 bytes for its own calls.
-/

namespace VG.Generic.Poly1305Blocks.X86_64.Poly1305

open VG.Proof.Poly1305.X86_64 (BlocksImpl)

/-- Which implementation of `vg_poly1305_blocks` an instance calls. -/
def note (v : BlocksImpl) : String :=
  "This implementation absorbs the whole blocks of the data with `" ++ v.name ++
    "`, and saves its caller's callee-saved registers in `scratch`."

def artifacts (v : BlocksImpl) : List Artifact := [
  { Spec.Poly1305.updateApi with
    name := Spec.Poly1305.updateApi.name ++ v.suffix
    target := X86_64.target
    doc := Spec.Poly1305.updateApi.doc (notes := [note v])
    code := Impl.Poly1305.X86_64.update v.name v.code
    contract := Spec.Poly1305.updateContract X86_64.abi 24
    stack := 24
    verified := Proof.Poly1305.X86_64.update_verified v
    spSafe := Proof.Poly1305.X86_64.update_spSafe v
    features := v.features }]

end VG.Generic.Poly1305Blocks.X86_64.Poly1305
