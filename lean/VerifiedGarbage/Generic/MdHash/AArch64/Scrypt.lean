import VerifiedGarbage.TCB.AArch64.Target
import VerifiedGarbage.Proof.Scrypt.AArch64.Whole.Verified

/-!
# scrypt (RFC 7914 §6) on AArch64, over SHA-256

A generic file (see `TCB/Emit.lean`): `vg_scrypt`, calling the
`vg_pbkdf2_hmac_sha256` made with the variant's SHA-256 compression function
(and `vg_scrypt_romix`), is emitted for every SHA-256 variant carried by
`MdHash.sha256`, named with its suffix (e.g. `vg_scrypt_sha2`), and needs its
CPU features. Other hash functions emit no scrypt artifact.

The stack is 96 bytes: a 16-byte frame saving `x30`, a 64-byte one, and the
16 bytes the frames of the functions called may use.
-/

namespace VG.Generic.MdHash.AArch64.Scrypt

open VG.Proof.Scrypt.AArch64.Whole (pbkName pbkOf scrypt_verified)

def artifacts (v : Proof.Pbkdf2.Md.AArch64.MdHash) : List Artifact :=
  match v.sha256 with
  | none => []
  | some c => [
    { Spec.Scrypt.scryptApi with
      name := Spec.Scrypt.scryptApi.name ++ c.suffix
      target := AArch64.target
      doc := Spec.Scrypt.scryptApi.doc (notes := ["Derives both keys with `" ++ pbkName c ++ "` and \
        runs scryptROMix on each block with `vg_scrypt_romix`, using the start of `scratch` as the \
        working space of each. The return address is saved in a 16-byte stack frame, and the \
        password, its length, `r`, `b`, `blen`, `v` and the next block in a 64-byte one below it; \
        the calls use the 16 bytes below that."])
      code := Impl.Scrypt.AArch64.scrypt (pbkName c) (pbkOf c)
      contract := Spec.Scrypt.scryptContract AArch64.abi 96
      stack := 96
      verified := scrypt_verified c
      spSafe := Code.all_of_forall (fun _ => rfl) _
      features := c.features }]

end VG.Generic.MdHash.AArch64.Scrypt
