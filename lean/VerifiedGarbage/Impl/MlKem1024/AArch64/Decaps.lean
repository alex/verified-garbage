import VerifiedGarbage.Impl.MlKem.AArch64.Decaps
import VerifiedGarbage.Impl.MlKem1024.AArch64.KeyGen

/-!
# ML-KEM-1024 on AArch64: `vg_mlkem1024_decaps`

ML-KEM-768's code (`Impl/MlKem/AArch64/Decaps.lean`) for the parameters of
ML-KEM-1024 (`lay1024`).
-/

namespace VG.Impl.MlKem1024.AArch64

open VG.AArch64

abbrev deAWith (c : Impl.Sha3.AArch64.Callee) : Prog isa := lay1024.deAWith c
abbrev deCWith (c : Impl.Sha3.AArch64.Callee) : Prog isa := lay1024.deCWith c
abbrev decapsWith (c : Impl.Sha3.AArch64.Callee) : Prog isa := lay1024.decapsWith c
abbrev decaps : Prog isa := decapsWith .scalar

end VG.Impl.MlKem1024.AArch64
