import VerifiedGarbage.Impl.MlKem.AArch64.Encode

/-!
# ML-KEM-1024 on AArch64: the encapsulation key check

`checkEk(ek = x0) -> w0`: the modulus check of ML-KEM-1024, the loop of
ML-KEM-768's (`checkEkBody`) over the 512 groups of 3 bytes of
`ek[0 : 1536]`: their two 12-bit fields `f`, each counted in `x10` if
`q - 1 - f` is negative; returns 1 if the count is 0 (`x10 - 1` negative),
and 0 otherwise. Every address and branch depends only on the pointer.
-/

namespace VG.Impl.MlKem1024.AArch64

open VG.AArch64
open VG.Impl.MlKem.AArch64 (checkEkBody)

def checkEk : Prog isa :=
  .seq (.block [.movz .x .x9 3328 0, .movz .x .x10 0 0, .movz .x .x11 512 0, .movz .x .x14 15 0]) <|
  .seq (.loop (.block checkEkBody) (.nonzero .x .x11))
    (.block [.subImm .x .x0 .x10 1, .lsr .x .x0 .x0 63])

end VG.Impl.MlKem1024.AArch64
