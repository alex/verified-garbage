import VerifiedGarbage.TCB.X86.Target
import VerifiedGarbage.Proof.MlDsa.X86.Round.Power2Round
import VerifiedGarbage.Proof.MlDsa.X86.Round.Bits
import VerifiedGarbage.Proof.MlDsa.X86.Round.NormLt
import VerifiedGarbage.Proof.MlDsa.X86.Round.HintF

/-!
# ML-DSA (FIPS 204) on x86: rounding and hints

The functions call no other one, and save their caller's registers in a
frame of 16 bytes below the return address (`stack := 16`).
`vg_mldsa_make_hint` and `vg_mldsa_use_hint` overwrite the argument `gamma2`
on the stack (which their contracts allow).
-/

namespace VG.Artifacts.MlDsaRound.X86

open VG.Proof.MlDsa.X86.Round

def artifacts : List Artifact := [
  { Spec.MlDsa.power2RoundApi with
    target := X86.target
    doc := Spec.MlDsa.power2RoundApi.doc
    code := Impl.MlDsa.X86.Round.power2Round
    contract := Spec.MlDsa.power2RoundContract X86.abi 16
    stack := 16
    verified := power2Round_verified
    spSafe := Code.all_of_allInstrs (by decide +kernel) },
  { Spec.MlDsa.highBitsApi with
    target := X86.target
    doc := Spec.MlDsa.highBitsApi.doc
    code := Impl.MlDsa.X86.Round.highBits
    contract := Spec.MlDsa.highBitsContract X86.abi 16
    stack := 16
    verified := highBits_verified
    spSafe := Code.all_of_allInstrs (by decide +kernel) },
  { Spec.MlDsa.lowBitsApi with
    target := X86.target
    doc := Spec.MlDsa.lowBitsApi.doc
    code := Impl.MlDsa.X86.Round.lowBits
    contract := Spec.MlDsa.lowBitsContract X86.abi 16
    stack := 16
    verified := lowBits_verified
    spSafe := Code.all_of_allInstrs (by decide +kernel) },
  { Spec.MlDsa.normLtApi with
    target := X86.target
    doc := Spec.MlDsa.normLtApi.doc
    code := Impl.MlDsa.X86.Round.normLt
    contract := Spec.MlDsa.normLtContract X86.abi 16
    stack := 16
    verified := normLt_verified
    spSafe := Code.all_of_allInstrs (by decide +kernel) },
  { Spec.MlDsa.makeHintApi with
    target := X86.target
    doc := Spec.MlDsa.makeHintApi.doc
    code := Impl.MlDsa.X86.Round.makeHint
    contract := Spec.MlDsa.makeHintContract X86.abi 16
    stack := 16
    verified := makeHint_verified
    spSafe := Code.all_of_allInstrs (by decide +kernel) },
  { Spec.MlDsa.useHintApi with
    target := X86.target
    doc := Spec.MlDsa.useHintApi.doc
    code := Impl.MlDsa.X86.Round.useHint
    contract := Spec.MlDsa.useHintContract X86.abi 16
    stack := 16
    verified := useHint_verified
    spSafe := Code.all_of_allInstrs (by decide +kernel) }]

end VG.Artifacts.MlDsaRound.X86
