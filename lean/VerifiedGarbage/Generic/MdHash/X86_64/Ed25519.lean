import VerifiedGarbage.TCB.X86_64.Target
import VerifiedGarbage.Proof.Ed25519.X86_64.PublicKey.Verified
import VerifiedGarbage.Proof.Ed25519.X86_64.VerifyMessage.Verified
import VerifiedGarbage.Proof.Ed25519.X86_64.SignCached.Verified
import VerifiedGarbage.Proof.Ed25519.X86_64.VerifyLit
import VerifiedGarbage.Proof.Ed25519.X86_64.Ifma.Window

/-!
# Ed25519 (RFC 8032) on x86-64, over SHA-512

Complete key derivation, cached-key signing, and verification are emitted
for every SHA-512 compression backend carried by `MdHash.sha512`, and for
each field multiplication of the Ed25519 functions they call (the baseline's,
and BMI2's and ADX's, `_adx`), and verification for its doublings with
AVX512_IFMA (`_ifma`). Each operation includes its streaming hash calls and
carries the backend's suffix and CPU features, then the field's.
Other hash families emit no Ed25519 artifacts.
-/

namespace VG.Generic.MdHash.X86_64.Ed25519

/-- Verification with the SHA-512 implementation `c`, the field multiplications
`fld` and the doublings `dbl`, those of `vg_ed25519_verify_equation` with the
suffix `fs`, which need the CPU features `ff`. -/
def verifyWith (c : Proof.Sha512.X86_64.Compress) (fld : Impl.Ed25519.X86_64.Arith)
    [Proof.Ed25519.X86_64.EdArith fld] (dbl : Prog X86_64.isa) [Proof.Ed25519.X86_64.EdDouble dbl]
    (fs : String) (ff : List String)
    (hq : Proof.Ed25519.X86_64.VerifyMessage.EqCode (Impl.Ed25519.X86_64.verifyEquation fld dbl)) :
    Artifact :=
  { Spec.Ed25519.verifyApi with
    name := Spec.Ed25519.verifyApi.name ++ c.suffix ++ fs
    target := X86_64.target
    doc := Spec.Ed25519.verifyApi.doc (notes := ["Hashes R, the public key and the message with \
      the selected SHA-512 backend, reduces the challenge modulo L, and calls \
      `vg_ed25519_verify_equation" ++ fs ++ "`. The digest and zero-extended reduced challenge \
      occupy separate buffers in a 168-byte stack frame; calls use another 16 bytes below it."])
    code := Impl.Ed25519.X86_64.VerifyMessage.code fld dbl fs c.callee c.suffix
    contract := Spec.Ed25519.verifyContract X86_64.abi 184
    stack := 184
    verified := Proof.Ed25519.X86_64.VerifyMessage.verified hq c
    spSafe := Proof.Ed25519.X86_64.VerifyMessage.spSafe hq c
    features := c.features ++ ff.filter (!c.features.contains ·) }

/-- The three operations with the SHA-512 implementation `c` and the field
multiplications `fld` (verification's doublings too), those of the Ed25519
functions with the suffix `fs`, which need the CPU features `ff`. -/
def withField (c : Proof.Sha512.X86_64.Compress) (fld : Impl.Ed25519.X86_64.Arith)
    [Proof.Ed25519.X86_64.EdArith fld] (fs : String) (ff : List String)
    (hq : Proof.Ed25519.X86_64.VerifyMessage.EqCode
      (Impl.Ed25519.X86_64.verifyEquation fld (Impl.Ed25519.X86_64.double4 fld))) :
    List Artifact := [
    { Spec.Ed25519.publicKeyApi with
      name := Spec.Ed25519.publicKeyApi.name ++ c.suffix ++ fs
      target := X86_64.target
      doc := Spec.Ed25519.publicKeyApi.doc (notes := ["Hashes the seed with `vg_sha512_init`, \
        `vg_sha512_update" ++ c.suffix ++ "` and `vg_sha512_finalize" ++ c.suffix ++ "`, keeping \
        the state and the digest in `scratch`, and encodes `[s]B` with \
        `vg_ed25519_scalar_base" ++ fs ++ "`. The pruned scalar `s` is kept in a \
        56-byte stack frame with the pointers and cleared before the frame is popped; the calls \
        use the 16 bytes below it."])
      code := Impl.Ed25519.X86_64.publicKey fld fs c.callee c.suffix
      contract := Spec.Ed25519.publicKeyContract X86_64.abi 72
      stack := 72
      verified := Proof.Ed25519.X86_64.PublicKey.publicKey_verified c
      spSafe := Proof.Ed25519.X86_64.PublicKey.publicKey_spSafe c
      features := c.features ++ ff.filter (!c.features.contains ·) },
    verifyWith c fld (Impl.Ed25519.X86_64.double4 fld) fs ff hq,
    { Spec.Ed25519.signCachedApi with
      name := Spec.Ed25519.signCachedApi.name ++ c.suffix ++ fs
      target := X86_64.target
      doc := Spec.Ed25519.signCachedApi.doc (notes := ["Computes all three SHA-512 hashes with \
        the selected backend, reduces the nonce and challenge, encodes the nonce point \
        with `vg_ed25519_scalar_base" ++ fs ++ "`, and computes the final scalar. \
        The 248-byte stack frame holds the pruned scalar, nonce prefix, nonce, challenge, digest \
        and saved arguments; its secret buffers are cleared before return. Calls use another 16 \
        bytes below the frame."])
      code := Impl.Ed25519.X86_64.SignCached.code fld fs c.callee c.suffix
      contract := Spec.Ed25519.signCachedContract X86_64.abi 264
      stack := 264
      verified := Proof.Ed25519.X86_64.SignCached.verified c
      spSafe := Proof.Ed25519.X86_64.SignCached.spSafe c
      features := c.features ++ ff.filter (!c.features.contains ·) }]

/-- Each operation with the SHA-512 implementation of `v`, if it has one, and
each field multiplication of the Ed25519 functions: the baseline's, and
BMI2's and ADX's (`_adx`); and verification with the doublings of
AVX512_IFMA too (`_ifma`). -/
def artifacts (v : Proof.Pbkdf2.Md.X86_64.MdHash) : List Artifact :=
  match v.sha512 with
  | none => []
  | some c => withField c Impl.X25519.X86_64.baseline "" []
        ⟨by lit_decide, by lit_decide, by lit_decide, Code.all_of_allInstrs (by lit_decide)⟩ ++
      withField c Impl.X25519.X86_64.adx "_adx" ["bmi2", "adx"]
        ⟨by lit_decide, by lit_decide, by lit_decide, Code.all_of_allInstrs (by lit_decide)⟩ ++
      [verifyWith c Impl.X25519.X86_64.adx Impl.Ed25519.X86_64.Ifma.double4 "_ifma"
        ["avx", "avx2", "bmi2", "adx", "avx512ifma", "avx512vl"]
        ⟨by lit_decide, by lit_decide, by lit_decide, Code.all_of_allInstrs (by lit_decide)⟩]

end VG.Generic.MdHash.X86_64.Ed25519
