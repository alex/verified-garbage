import VerifiedGarbage.Impl.MlKem.X86.CheckEk

/-!
# ML-KEM-1024 on x86 (32-bit): `vg_mlkem1024_check_ek`

The loop of `vg_mlkem768_check_ek` (`Impl/MlKem/X86/CheckEk.lean`: `ekBody`
and `ekEnd`) over the 512 groups of three bytes of the first 1536 bytes of
`ek`. Every address and branch depends only on the pointer.
-/

namespace VG.Impl.MlKem1024.X86

open VG.X86 VG.Impl.MlKem.X86

/-- `esi = ek`, `ecx = 512`, `ebx = 0xffffffff`. -/
def ekInit512 : List Instr :=
  [.mov .esi (.mem (at_ .esp 20)), .mov .ecx (.imm 512), .mov .ebx (.imm 0xffffffff)]

def checkEk : Prog isa := leaf (.seq (.block ekInit512) (.seq (.loop (.block ekBody) .ne) (.block ekEnd)))

end VG.Impl.MlKem1024.X86
