import VerifiedGarbage.Impl.MlKem.AArch64.Encode

/-!
# ML-KEM-1024 on AArch64: the encapsulation key check

`checkEk(ek = x0) -> w0`: the modulus check of ML-KEM-1024, ML-KEM-768's
(`checkEkWith`) for the 512 groups of 3 bytes of `ek[0 : 1536]`. Every
address and branch depends only on the pointer.
-/

namespace VG.Impl.MlKem1024.AArch64

open VG.AArch64

abbrev checkEk : Prog isa := Impl.MlKem.AArch64.checkEkWith 512

end VG.Impl.MlKem1024.AArch64
