import VerifiedGarbage.Proof.AesGcm.X86.Contract
import VerifiedGarbage.Proof.Framework.Contract

namespace VG.Proof.AesGcm.X86
open VG VG.X86

def saSat : State where
  gpr r := match r with | .esp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if a = 0x8005 then 0x10 else if a = 0x8009 then 0x30
    else if a = 0x8015 then 0x20 else if a = 0x801d then 0x40 else 0
  rd := [⟨0x1000, 256⟩, ⟨0x2000, 0⟩]
  wr := [⟨0x3000, 80⟩, ⟨0x4000, 2560⟩, ⟨0x8004, 28⟩]

example : streamAadX86.Implies (Spec.Gcm.streamAadContract X86.abi 24) := by
    have a0 : arg saSat 0 = 0x1000 := by decide
    have a1 : arg saSat 1 = 0x3000 := by decide
    have a2 : arg saSat 2 = 0 := by decide
    have a3 : arg saSat 3 = 0 := by decide
    have a4 : arg saSat 4 = 0x2000 := by decide
    have a5 : arg saSat 5 = 0 := by decide
    have a6 : arg saSat 6 = 0x4000 := by decide
    have e : argAddr saSat 0 = 0x8004 := by decide
    have esp : saSat.gpr .esp = 0x8000 := rfl
    sig_implies [Spec.Gcm.streamAadContract, Spec.Gcm.streamAadSig, streamAadX86, streamAadPre, pubN,
      X86.abi, X86.argSlots, X86.argVal, X86.argBytes] [a0, a1, a2, a3, a4, a5, a6, e, esp] using saSat

end VG.Proof.AesGcm.X86
