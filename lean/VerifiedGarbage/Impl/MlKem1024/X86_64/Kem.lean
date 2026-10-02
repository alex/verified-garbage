import VerifiedGarbage.Impl.MlKem.X86_64.KeyGen
import VerifiedGarbage.Impl.MlKem.X86_64.Encaps
import VerifiedGarbage.Impl.MlKem.X86_64.Decaps
import VerifiedGarbage.Impl.MlKem.X86_64.CheckEk
import VerifiedGarbage.Impl.MlKem1024.X86_64.Compress

/-!
# ML-KEM-1024 on x86-64: `vg_mlkem1024_keygen`, `vg_mlkem1024_encaps`, `vg_mlkem1024_decaps` and `vg_mlkem1024_check_ek`

The key generation, encapsulation and decapsulation of ML-KEM
(`Impl/MlKem/X86_64/`) for ML-KEM-1024 (`kem1024`): `k = 4`, `d_u = 11`
and `d_v = 5`, which `vg_mlkem1024_compress_encode` and
`vg_mlkem1024_decode_decompress` (`Compress.lean`) take. The 16 entries of
`Â` are polynomials 17–32 of the working space (`Â[i, j]` is polynomial
`17 + 4i + j`), after the accumulator (polynomial 15) and the products
(polynomial 16), and the ciphertext of the re-encryption (1568 bytes) is in
polynomials 33 and 34; the outputs of `PRF₂` are in polynomials 38 and 39,
and the working space of their computation and of `vg_mlkem_sample_ntt4`
from polynomial 35. `scratch` is 48 KiB (44 polynomials).
-/

namespace VG.Impl.MlKem1024.X86_64

open VG.X86_64 VG.Impl.MlKem.X86_64

/-- ML-KEM-1024. -/
def kem1024 : Kem where
  p := Spec.MlKem.mlKem1024
  scr := 49152
  pA := 17
  pW := 35
  pPR := 38
  pCT := 33
  ceN := "vg_mlkem1024_compress_encode"
  ce := compressEncode1024
  ddN := "vg_mlkem1024_decode_decompress"
  dd := decodeDecompress1024

abbrev keyGen1024 (c : Callee4) : Prog isa := kemKeyGen kem1024 c
abbrev encaps1024 (c : Callee4) : Prog isa := kemEncaps kem1024 c
abbrev decaps1024 (c : Callee4) : Prog isa := kemDecaps kem1024 c
abbrev checkEk1024 : Prog isa := checkEkK 4

end VG.Impl.MlKem1024.X86_64
