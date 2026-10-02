import VerifiedGarbage.TCB.X86.Target
import VerifiedGarbage.Proof.Sha256.X86.Variants.Interface
import VerifiedGarbage.Proof.Scrypt.X86.Whole.Verified

/-!
# scrypt (RFC 7914 §6) on x86, over SHA-256

A generic file (see `TCB/Emit.lean`): `vg_scrypt`, calling the
`vg_pbkdf2_hmac_sha256` made with the backend's SHA-256 functions (and
`vg_scrypt_romix`), is emitted for every x86 SHA-256 backend, named with its
suffix (e.g. `vg_scrypt_shani`), and needs its CPU features. **Review
note**: `sig` and `doc` are trusted, as they tie the Rust caller to the
contract: they are those of the function's `Api` (`Spec/Scrypt/Contract.lean`),
and this file adds only notes on the implementation. The emitter adds the
`# Safety` items that depend on the target (`Sig.layoutDoc`), from `stack`
and `writeArgs`, which `ofSig` checks against the contract.

The stack is 116 bytes: a 36-byte frame, the return address of a call, and
the 76 bytes `vg_pbkdf2_hmac_sha256` uses.
-/

namespace VG.Generic.Sha256.X86.Scrypt

open VG.Proof.Scrypt.X86.Whole (pbkName pbkOf scrypt_verified scrypt_spSafe)

def artifacts (v : Proof.Sha256.X86.Variants.Backend) : List Artifact := [
  { Spec.Scrypt.scryptApi with
    name := Spec.Scrypt.scryptApi.name ++ v.suffix
    target := X86.target
    doc := Spec.Scrypt.scryptApi.doc (notes := ["Derives both keys with `" ++ pbkName v ++ "` and runs \
      scryptROMix on each block with `vg_scrypt_romix`, using the start of `scratch` as the working \
      space of each. The arguments of each call and the next block are kept in a 36-byte stack \
      frame; our own arguments are read from the stack whenever they are needed, and the calls use \
      the 80 bytes below the frame."])
    code := Impl.Scrypt.X86.scrypt (pbkName v) (pbkOf v)
    contract := Spec.Scrypt.scryptContract X86.abi 116
    stack := 116
    verified := scrypt_verified v
    spSafe := scrypt_spSafe v
    features := v.features }]

end VG.Generic.Sha256.X86.Scrypt
