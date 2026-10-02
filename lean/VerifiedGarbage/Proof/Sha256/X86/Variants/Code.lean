import VerifiedGarbage.Impl.Pbkdf2.Md.X86
import VerifiedGarbage.Impl.Pbkdf2.Whole.X86
import VerifiedGarbage.Impl.Sha256.X86.Stream
import VerifiedGarbage.Spec.Sha256.Contract
import VerifiedGarbage.Spec.Pbkdf2.Generic

/-!
# SHA-256 backends on x86: the code built on them

SHA-256 has backends on x86 (`Interface.lean`): implementations of its
compression function, each with the streaming `update` and `finalize` made
with it. HMAC and PBKDF2 are the code of every other hash function, at
SHA-256 made with a backend: its streaming functions as HMAC's `init` calls
them (`hmacHash`), SHA-256 as a Merkle–Damgård hash function for HMAC's
`finalize` and PBKDF2's iteration, which call the compression function
(`mdHash`, `Impl/Pbkdf2/Md/X86.lean`), and the functions the whole of PBKDF2
calls (`fns`, `Impl/Pbkdf2/Whole/X86.lean`), by the names the generic
registration files give them (with the backend's suffix).
-/

namespace VG.Proof.Sha256.X86.Variants

open VG.X86

/-- SHA-256's streaming functions, with a backend's `update` and `finalize`
(`updC`, `finC`), named with its suffix: a 96-byte state, 20 words of working
space and a 32-byte digest. -/
def hmacHash (suffix : String) (updC finC : Prog isa) : Impl.Hmac.Generic.X86.Hash :=
  ⟨64, 96, 32, 32, 20, Spec.Sha256.initApi.name, Impl.Sha256.X86.Stream.init,
    Spec.Sha256.updateApi.name ++ suffix, updC, Spec.Sha256.finalizeApi.name ++ suffix, finC⟩

/-- SHA-256 as a Merkle–Damgård hash function, with a backend's compression
function `cmpN`/`cmpC` and the streaming functions calling it: a 32-byte hash
value, a big-endian 8-byte length field, and 112 bytes of scratch space for
the compression function. -/
def mdHash (suffix cmpN : String) (cmpC updC finC : Prog isa) : Impl.Pbkdf2.Md.X86.Hash :=
  ⟨hmacHash suffix updC finC, 32, 8, true, 112, cmpN, cmpC, Impl.Sha256.X86.Stream.params.out⟩

/-- The functions the whole of PBKDF2 calls for SHA-256 with a backend. -/
def fns (suffix cmpN : String) (cmpC updC finC : Prog isa) : Impl.Pbkdf2.Whole.X86.Fns where
  H := hmacHash suffix updC finC
  W := Spec.Hmac.sha256I.scratch
  hiN := Spec.Hmac.sha256I.initApi.name ++ suffix
  hiC := (hmacHash suffix updC finC).init
  hfN := Spec.Hmac.sha256I.finalizeApi.name ++ suffix
  hfC := (mdHash suffix cmpN cmpC updC finC).hmacFin
  itN := Spec.Hmac.sha256I.iterateApi.name ++ suffix
  itC := (mdHash suffix cmpN cmpC updC finC).iterate

end VG.Proof.Sha256.X86.Variants
