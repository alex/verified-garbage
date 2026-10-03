import VerifiedGarbage.Impl.MlKem.X86.KeyGen
import VerifiedGarbage.Impl.MlKem.X86.Encaps
import VerifiedGarbage.Impl.MlKem.X86.Decaps
import VerifiedGarbage.Impl.MlKem.X86.CheckEk
import VerifiedGarbage.Impl.MlKem1024.X86.Compress

/-!
# ML-KEM-1024 on x86 (32-bit): `vg_mlkem1024_keygen`, `_encaps`, `_decaps` and `_check_ek`

The code of ML-KEM-768 (`Impl/MlKem/X86/`) for the parameter set of
ML-KEM-1024 (`L1024`: `k = 4`, `d_u = 11`, `d_v = 5`, and `scratch` of 49152
bytes, laid out as `Impl/MlKem/X86/Kem.lean` says), which compresses to 5 and
11 bits with `vg_mlkem1024_compress_encode` and
`vg_mlkem1024_decode_decompress` (`Compress.lean`). The key check loops over
the 512 groups of three bytes of `ek[0 : 1536]`.
-/

namespace VG.Impl.MlKem1024.X86

open VG.X86 VG.Impl.MlKem.X86

/-- ML-KEM-1024. -/
def L1024 : KemLay where
  p := Spec.MlKem.mlKem1024
  scratch := 49152
  kgT := 8192
  kgA := 9216
  kgP := 10240
  kgNS := 11264
  kgSS := 12288
  kgST := 14336
  kgWK := 14536
  kgRS := 15176
  kgPRF := 15248
  kgACC := 15376
  eE := 4096
  eU := 5120
  eA := 6144
  eP := 7168
  eT := 8192
  eMU := 9216
  eNS := 10240
  eSS := 11264
  eST := 13312
  eWK := 13512
  ePRF := 14152
  eACC := 14280
  eEK := 14284
  eM := 15856
  eKR := 15888
  eC := 15956
  eH := 17528
  ceName := "vg_mlkem1024_compress_encode"
  ceCode := compressEncode
  ddName := "vg_mlkem1024_decode_decompress"
  ddCode := decodeDecompress

def keyGen : Prog isa := leaf (kgBody L1024)
def encaps : Prog isa := leaf (encapsBody L1024)
def decaps : Prog isa := leaf (decapsBody L1024)
def checkEk : Prog isa := checkEkN 512

end VG.Impl.MlKem1024.X86
