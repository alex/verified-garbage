import VerifiedGarbage.Impl.MlKem.AArch64.KeyGen
import VerifiedGarbage.Impl.MlKem1024.AArch64.Compress

/-!
# ML-KEM-1024 on AArch64: `vg_mlkem1024_keygen`

ML-KEM-768's code (`Impl/MlKem/AArch64/KeyGen.lean`) for the parameters of
ML-KEM-1024 (`lay1024`): `k = 4`, `d_u = 11` and `d_v = 5`, with 48 KiB of
`scratch` and ML-KEM-1024's compression functions.
-/

namespace VG.Impl.MlKem1024.AArch64

open VG.AArch64

/-- ML-KEM-1024: `k = 4`, `d_u = 11`, `d_v = 5`, 48 KiB of `scratch`. -/
def lay1024 : Impl.MlKem.AArch64.KemLay where
  k := 4
  du := 11
  dv := 5
  scl := 49152
  ceName := "vg_mlkem1024_compress_encode"
  ce := compressEncode
  ddName := "vg_mlkem1024_decode_decompress"
  dd := decodeDecompress

abbrev kgAWith (c : Impl.Sha3.AArch64.Callee) : Prog isa := lay1024.kgAWith c
abbrev kgCWith (c : Impl.Sha3.AArch64.Callee) : Prog isa := lay1024.kgCWith c
abbrev keyGenWith (c : Impl.Sha3.AArch64.Callee) : Prog isa := lay1024.keyGenWith c
abbrev keyGen : Prog isa := keyGenWith .scalar

end VG.Impl.MlKem1024.AArch64
