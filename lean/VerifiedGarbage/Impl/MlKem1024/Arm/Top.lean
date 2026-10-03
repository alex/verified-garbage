import VerifiedGarbage.Impl.MlKem.Arm.Top
import VerifiedGarbage.Impl.MlKem1024.Arm.Poly

/-!
# ML-KEM-1024 on 32-bit ARM: key generation, encapsulation, decapsulation

The functions of ML-KEM-768 (`Impl/MlKem/Arm/Top.lean`) for `k = 4`,
`d_u = 11` and `d_v = 5`, which compress with `vg_mlkem1024_compress_encode`
and `vg_mlkem1024_decode_decompress` (and the message, to and from 1 bit,
with ML-KEM-768's). `scratch` holds polynomials `0` to `16` from 2048, the
working spaces of the callees at 19456, `c'` at 22528 and the copy of `c`
at 24576: its first 26144 bytes (of 49152).

The keys and ciphertexts are laid out as FIPS 203 says: `ek` is
`ByteEncode₁₂(t̂)` (1536 bytes) then `ρ`; `dk` is `ByteEncode₁₂(ŝ)`, `ek`
(at 1536), `H(ek)` (at 3104) and `z` (at 3136); `c` is the four
`ByteEncode₁₁(Compress₁₁(u[i]))` (352 bytes each) then
`ByteEncode₅(Compress₅(v))` (at 1408).
-/

namespace VG.Impl.MlKem1024.Arm

open VG.Arm
open VG.Impl.MlKem.Arm (KemLay)

/-- ML-KEM-1024's parameters. -/
def kl1024 : KemLay :=
  ⟨Spec.MlKem.mlKem1024, 49152, [8, 6, 5], "vg_mlkem1024_compress_encode", compressEncode1024,
    "vg_mlkem1024_decode_decompress", decodeDecompress1024⟩

abbrev keygen1024 : Prog isa := kl1024.keygen
abbrev encaps1024 : Prog isa := kl1024.encaps
abbrev decaps1024 : Prog isa := kl1024.decaps

end VG.Impl.MlKem1024.Arm
