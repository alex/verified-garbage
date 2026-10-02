import VerifiedGarbage.Proof.Aes.X86.AesNi.KeyDispatch
import VerifiedGarbage.Proof.Aes.X86.AesNi.KeyBranches
import VerifiedGarbage.Proof.Aes.X86.AesNi.CT
import VerifiedGarbage.Proof.Aes.X86.ExpandKey
import VerifiedGarbage.Spec.Aes.Contract
import VerifiedGarbage.Proof.Framework.Contract

namespace VG.Proof.Aes.X86.AesNi
open VG VG.X86
open VG.Proof.Aes.X86 (EPre keyLen ekSat)


theorem expandKey_correct (bodies : KeyBodies) (s : State) (hs : Proof.Aes.expandKeyX86.pre s) :
    ∃ t s', Exec isa Impl.Aes.X86.AesNi.expandKey s t s' ∧ abiPreserved s s' ∧
      Proof.Aes.expandKeyX86.post s s' :=
  (key_dispatch_correct bodies (EPre.of hs)).imp fun _ ⟨s', he, h⟩ => ⟨s', he, h⟩

theorem expandKey_verified (bodies : KeyBodies) :
    Verified X86.target Impl.Aes.X86.AesNi.expandKey (Spec.Aes.expandKeyContract X86.abi) :=
  Verified.of_correct (expandKey_correct bodies) expandKey_ct (by
    have a0 : arg ekSat 0 = 0x1000 := by decide
    have a1 : arg ekSat 1 = 16 := by decide
    have a2 : arg ekSat 2 = 0x2000 := by decide
    have a3 : arg ekSat 3 = 0x3000 := by decide
    have e : argAddr ekSat 0 = 0x8004 := by decide
    have esp : ekSat.gpr .esp = 0x8000 := rfl
    sig_implies [Spec.Aes.expandKeyContract, Spec.Aes.expandKeySig, X86.abi, X86.argSlots,
      X86.argVal, X86.argBytes, Proof.Aes.expandKeyX86] [a0, a1, a2, a3, e, esp] using ekSat)

end VG.Proof.Aes.X86.AesNi
