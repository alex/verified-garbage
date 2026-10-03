import VerifiedGarbage.TCB.X86_64.Target
import VerifiedGarbage.Proof.Ed448.X86_64.Verify.Verified

/-!
# Ed448 verification on x86-64

The signature and documentation come from the reviewed Ed448 API.
-/

namespace VG.Artifacts.Ed448Verify.X86_64

def artifacts : List Artifact := [
  { Spec.Ed448.verifyApi with
    target := X86_64.target
    doc := Spec.Ed448.verifyApi.doc (notes := ["Uses baseline integer instructions. Returns 0 \
      at once for a context of 256 bytes or more. Otherwise writes the first ten bytes of \
      dom4(0, C) into a stack frame, hashes them, the context, R, the public key and the \
      message with `vg_keccak_absorb`, `vg_keccak_pad` and `vg_keccak_squeeze` (SHAKE256, \
      with the Keccak state and the sponge functions' working space in `scratch`) into the \
      frame, reduces the hash modulo L there with `vg_ed448_scalar_reduce`, and returns \
      `vg_ed448_verify_equation`'s result. The frame (the hash and k) is not cleared: \
      verification has no secrets."])
    code := Impl.Ed448.X86_64.Verify.verify
    contract := Spec.Ed448.verifyContract X86_64.abi 272
    stack := 272
    verified := Proof.Ed448.X86_64.Verify.verify_verified
    spSafe := Code.all_of_allInstrs (by lit_decide) }]

end VG.Artifacts.Ed448Verify.X86_64
