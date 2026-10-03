import VerifiedGarbage.TCB.X86_64.Target
import VerifiedGarbage.Proof.Ed448.X86_64.PublicKey.Verified

/-!
# Ed448 public-key derivation on x86-64

The signature and documentation come from the reviewed Ed448 API.
-/

namespace VG.Artifacts.Ed448PublicKey.X86_64

def artifacts : List Artifact := [
  { Spec.Ed448.publicKeyApi with
    target := X86_64.target
    doc := Spec.Ed448.publicKeyApi.doc (notes := ["Uses baseline integer instructions. \
      Hashes the private key with `vg_keccak_absorb`, `vg_keccak_pad` and \
      `vg_keccak_squeeze` (SHAKE256, into `scratch`), prunes the first 57 bytes of the hash \
      into a stack frame, encodes `[s]B` with `vg_ed448_scalar_base`, and clears the frame's \
      copy of the scalar. The rest of the hash, and the base-point multiplication's working \
      values, are left in `scratch`."])
    code := Impl.Ed448.X86_64.publicKey
    contract := Spec.Ed448.publicKeyContract X86_64.abi 104
    stack := 104
    verified := Proof.Ed448.X86_64.PublicKey.publicKey_verified
    spSafe := Code.all_of_allInstrs (by lit_decide) }]

end VG.Artifacts.Ed448PublicKey.X86_64
