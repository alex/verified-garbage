import VerifiedGarbage.Impl.MlKem.AArch64.Encaps
import VerifiedGarbage.Impl.MlKem1024.AArch64.KeyGen

/-!
# ML-KEM-1024 on AArch64: `vg_mlkem1024_encaps`

ML-KEM-768's code (`Impl/MlKem/AArch64/Encaps.lean`) for the parameters of
ML-KEM-1024 (`lay1024`).
-/

namespace VG.Impl.MlKem1024.AArch64

open VG.AArch64

abbrev enAWith (c : Impl.Sha3.AArch64.Callee) : Prog isa := lay1024.enAWith c
abbrev enCWith (c : Impl.Sha3.AArch64.Callee) : Prog isa := lay1024.enCWith c
abbrev encapsWith (c : Impl.Sha3.AArch64.Callee) : Prog isa := lay1024.encapsWith c
abbrev encaps : Prog isa := encapsWith .scalar

end VG.Impl.MlKem1024.AArch64
