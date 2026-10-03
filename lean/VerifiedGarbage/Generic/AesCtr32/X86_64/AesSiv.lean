import VerifiedGarbage.TCB.X86_64.Target
import VerifiedGarbage.Proof.AesSiv.X86_64.Verified

/-!
# AES-SIV (RFC 5297) on x86-64

A generic file (see `TCB/Emit.lean`): the artifacts it lists, calling an
implementation `v` of `vg_aes_ctr32` (through the CMAC functions made with
it, and directly for CTR), are emitted once for each implementation
(`Variants/AesCtr32/X86_64/`), named with its suffix (e.g.
`vg_aes_siv_seal_aesni`), and need its CPU features.

The stack is 16 bytes for each: the return addresses of the call of a CMAC
function (or of `vg_aes_ctr32`) and of its call of `vg_aes_ctr32`.
-/

namespace VG.Generic.AesCtr32.X86_64.AesSiv

open VG.Proof.AesSiv.X86_64

/-- Which functions an instance calls. -/
def note (v : Proof.Aes.X86_64.Ctr32Impl) : String :=
  "This implementation calls the CMAC functions made with `" ++ v.callee.name ++ "` (e.g. `" ++
    Spec.Cmac.aesUpdateApi.name ++ v.suffix ++ "`)."

/-- Which functions an instance of `seal` or `open` calls. -/
def cryptNote (v : Proof.Aes.X86_64.Ctr32Impl) : String :=
  "This implementation calls the CMAC functions made with `" ++ v.callee.name ++ "` (e.g. `" ++
    Spec.Cmac.aesUpdateApi.name ++ v.suffix ++ "`), and encrypts with `" ++ v.callee.name ++ "`."

def artifacts (v : Proof.Aes.X86_64.Ctr32Impl) : List Artifact := [
  { Spec.Siv.initApi with
    name := Spec.Siv.initApi.name ++ v.suffix
    target := X86_64.target
    doc := Spec.Siv.initApi.doc (notes := [
      "This implementation expands the keys with `" ++ v.expand.name ++ "` and computes the CMAC subkeys \
      with `" ++ Spec.Cmac.aesSubkeysApi.name ++ v.suffix ++ "`."])
    code := Impl.AesSiv.X86_64.init v.expand v.callee v.suffix
    contract := Spec.Siv.initContract X86_64.abi 16
    stack := 16
    verified := init_verified v
    spSafe := init_spSafe v
    features := v.features },
  { Spec.Siv.s2vStartApi with
    name := Spec.Siv.s2vStartApi.name ++ v.suffix
    target := X86_64.target
    doc := Spec.Siv.s2vStartApi.doc (notes := [note v])
    code := Impl.AesSiv.X86_64.s2vStart v.callee v.suffix
    contract := Spec.Siv.s2vStartContract X86_64.abi 16
    stack := 16
    verified := s2vStart_verified v
    spSafe := s2vStart_spSafe v
    features := v.features },
  { Spec.Siv.s2vAdApi with
    name := Spec.Siv.s2vAdApi.name ++ v.suffix
    target := X86_64.target
    doc := Spec.Siv.s2vAdApi.doc (notes := [note v])
    code := Impl.AesSiv.X86_64.s2vAd v.callee v.suffix
    contract := Spec.Siv.s2vAdContract X86_64.abi 16
    stack := 16
    verified := s2vAd_verified v
    spSafe := s2vAd_spSafe v
    features := v.features },
  { Spec.Siv.sealApi with
    name := Spec.Siv.sealApi.name ++ v.suffix
    target := X86_64.target
    doc := Spec.Siv.sealApi.doc (notes := [cryptNote v])
    code := Impl.AesSiv.X86_64.«seal» v.callee v.suffix
    contract := Spec.Siv.sealContract X86_64.abi 16
    stack := 16
    verified := seal_verified v
    spSafe := seal_spSafe v
    features := v.features },
  { Spec.Siv.openApi with
    name := Spec.Siv.openApi.name ++ v.suffix
    target := X86_64.target
    doc := Spec.Siv.openApi.doc (notes := [cryptNote v,
      "It compares the IVs and overwrites the data with zeros without a branch on the result."])
    code := Impl.AesSiv.X86_64.«open» v.callee v.suffix
    contract := Spec.Siv.openContract X86_64.abi 16
    stack := 16
    verified := open_verified v
    spSafe := open_spSafe v
    features := v.features }]

end VG.Generic.AesCtr32.X86_64.AesSiv
