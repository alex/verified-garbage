import VerifiedGarbage.TCB.AArch64.Target
import VerifiedGarbage.Impl.ChaCha20Poly1305.AArch64
import VerifiedGarbage.Proof.ChaCha20Poly1305.AArch64.Verified
import VerifiedGarbage.Proof.ChaCha20Poly1305.AArch64.Lit

/-!
# ChaCha20-Poly1305 (RFC 8439 §2.8) on AArch64

A generic caller (see `TCB/Emit.lean`), emitted for every ChaCha20 stream
backend. The one-time Poly1305 key uses the scalar block function. The
functions use no stack: their calls (`bl`) keep the return address in `x30`,
which they save in the context. With the eight-block stream
(`XorImpl.stitched`), the integer units absorb the data's whole chunks of 512
bytes into Poly1305 while the stream computes their keystream
(`Impl/ChaCha20Poly1305/AArch64/Stitched.lean`).
-/

namespace VG.Generic.ChaCha20Xor.AArch64.ChaCha20Poly1305

/-- Notes on the stitched implementation. -/
def notes (v : Proof.ChaCha20.AArch64.XorImpl) : List String :=
  if v.stitched then ["Absorbs each 512 bytes into Poly1305 with integer instructions while " ++
    "computing the keystream of the next with the eight-block ChaCha20 kernel."] else []

def artifacts (v : Proof.ChaCha20.AArch64.XorImpl) : List Artifact := [
  { Spec.ChaCha20Poly1305.sealApi with
    name := Spec.ChaCha20Poly1305.sealApi.name ++ v.callee.suffix
    features := v.features
    target := AArch64.target
    doc := Spec.ChaCha20Poly1305.sealApi.doc (notes := notes v)
    code := Impl.ChaCha20Poly1305.AArch64.sealCode v.callee v.stitched
    contract := Spec.ChaCha20Poly1305.sealContract AArch64.abi
    verified := Proof.ChaCha20Poly1305.AArch64.seal_verified v
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.ChaCha20Poly1305.openApi with
    name := Spec.ChaCha20Poly1305.openApi.name ++ v.callee.suffix
    features := v.features
    target := AArch64.target
    doc := Spec.ChaCha20Poly1305.openApi.doc (notes := notes v)
    code := Impl.ChaCha20Poly1305.AArch64.openCode v.callee v.stitched
    contract := Spec.ChaCha20Poly1305.openContract AArch64.abi
    verified := Proof.ChaCha20Poly1305.AArch64.open_verified v
    spSafe := Code.all_of_forall (fun _ => rfl) _ }]

end VG.Generic.ChaCha20Xor.AArch64.ChaCha20Poly1305
