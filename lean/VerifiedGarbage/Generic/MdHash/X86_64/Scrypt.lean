import VerifiedGarbage.TCB.X86_64.Target
import VerifiedGarbage.Proof.Scrypt.X86_64.Whole.Verified

/-!
# scrypt (RFC 7914 §6) on x86-64, over SHA-256

A generic file (see `TCB/Emit.lean`): `vg_scrypt`, calling the
`vg_pbkdf2_hmac_sha256` made with the variant's SHA-256 compression function
(and `vg_scrypt_romix`), is emitted for every SHA-256 variant carried by
`MdHash.sha256`, named with its suffix (e.g. `vg_scrypt_shani`), and needs
its CPU features. Other hash functions emit no scrypt artifact. **Review
note**: `sig` and `doc` are trusted, as they tie the Rust caller to the
contract: they are those of the function's `Api` (`Spec/Scrypt/Contract.lean`),
and this file adds only notes on the implementation. The emitter adds the
`# Safety` items that depend on the target (`Sig.layoutDoc`), from `stack`
and `writeArgs`, which `ofSig` checks against the contract.

The stack is 88 bytes: a 56-byte frame, the return address of a call, and
the 24 bytes `vg_pbkdf2_hmac_sha256`'s own calls use.
-/

namespace VG.Generic.MdHash.X86_64.Scrypt

open VG.Proof.Scrypt.X86_64.Whole (pbkName pbkOf scrypt_verified scrypt_spSafe)

def artifacts (v : Proof.Pbkdf2.Md.X86_64.MdHash) : List Artifact :=
  match v.sha256 with
  | none => []
  | some c => [
    { Spec.Scrypt.scryptApi with
      name := Spec.Scrypt.scryptApi.name ++ c.suffix
      target := X86_64.target
      doc := Spec.Scrypt.scryptApi.doc (notes := ["Derives both keys with `" ++ pbkName c ++ "` and \
        runs scryptROMix on each block with `vg_scrypt_romix`, using the start of `scratch` as the \
        working space of each. The password, its length, `r` and `b`, PBKDF2's stack arguments and \
        the next block are kept in a 56-byte stack frame; the calls use the 32 bytes below it."])
      code := Impl.Scrypt.X86_64.scrypt (pbkName c) (pbkOf c)
      contract := Spec.Scrypt.scryptContract X86_64.abi 88
      stack := 88
      verified := scrypt_verified c
      spSafe := scrypt_spSafe c
      features := c.features }]

end VG.Generic.MdHash.X86_64.Scrypt
