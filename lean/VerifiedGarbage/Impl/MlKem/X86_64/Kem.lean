import VerifiedGarbage.Impl.MlKem.X86_64.Frag
import VerifiedGarbage.Spec.MlKem

/-!
# ML-KEM on x86-64: what a parameter set fixes of the top-level functions

The key generation, encapsulation and decapsulation of ML-KEM-768 and
ML-KEM-1024 are the same code (`KeyGen.lean`, `Encrypt.lean`, `Encaps.lean`,
`Decaps.lean`) for a `Kem`: the rank `k` and the widths `d_u` and `d_v` of
the parameter set, the size of `scratch`, where the matrix, the outputs of
`PRF₂`, the working space of their computation and the ciphertext of the
re-encryption are among its polynomials (`Frag.lean`), and the compression
the widths `d_u` and `d_v` call. Loops over `k` are unrolled: `Â[i, j]` is
polynomial `pA + k i + j`, sampled four entries at a time and then one at a
time (`samples`), and a sum of `k` products is accumulated left to right
(`dotN`).
-/

namespace VG.Impl.MlKem.X86_64

open VG.X86_64

/-- What a parameter set fixes of the top-level functions. -/
structure Kem where
  /-- The parameter set (FIPS 203 Table 2): the rank `k`, and the widths
  `d_u` and `d_v`. -/
  p : Spec.MlKem.Params
  /-- The size of `scratch`, in bytes. -/
  scr : Nat
  /-- The polynomials of `Â` (from `pA`), of the working space of
  `vg_mlkem_sample_ntt4` and of `prfs` (from `pW`), of the outputs of `PRF₂`
  (from `pPR`), and of the ciphertext of the re-encryption (from `pCT`). -/
  pA : Nat
  pW : Nat
  pPR : Nat
  pCT : Nat
  /-- The compression and decompression to `d_u` and `d_v`. -/
  ceN : String
  ce : Prog isa
  ddN : String
  dd : Prog isa

namespace Kem

variable (L : Kem)

abbrev k : Nat := L.p.k
abbrev du : Nat := L.p.du
abbrev dv : Nat := L.p.dv

/-- The lengths of the encapsulation key, the decapsulation key and the ciphertext. -/
abbrev ekLen : Nat := L.p.ekLen
abbrev dkLen : Nat := L.p.dkLen
abbrev ctLen : Nat := L.p.ctLen

/-- The outputs of `PRF₂` (128 bytes each). -/
def oPR : Nat := oP L.pPR
/-- The working space of `prfs` (2368 bytes), as a lane (32 bytes). -/
def lPW : Nat := oP L.pW / 32
/-- The ciphertext of the re-encryption. -/
def oCT : Nat := oP L.pCT

/-- `Â[i, j]`: polynomial `pA + k i + j`. -/
abbrev aS (i j : Nat) : Ptr := pS (L.pA + L.k * i + j)

/-- `ByteEncode_d(Compress_d(f))` to `out`, for `d = d_u` or `d_v`. -/
def ceAt (f : Ptr) (d : Nat) (out : Ptr) : Prog isa := ceCall L.ceN L.ce f d out

/-- `Decompress_d(ByteDecode_d(b))` to `f`, for `d = d_u` or `d_v`. -/
def ddAt (b : Ptr) (d : Nat) (f : Ptr) : Prog isa := ddCall L.ddN L.dd b d f

/-- Entries `e, …, e + n - 1` of `Â` (entry `e = k i + j`), four at a time
(with `pW` as the working space) and the last `n mod 4` one at a time. -/
def ents (c : Callee4) : Nat → Nat → Prog isa
  | e, n + 5 => .seq (quad c L.k e (pS (L.pA + e)) (pS L.pW)) (ents c (e + 4) (n + 1))
  | e, 4 => quad c L.k e (pS (L.pA + e)) (pS L.pW)
  | e, n + 2 => .seq (sampleIJ (pS (L.pA + e)) (e / L.k) (e % L.k)) (ents c (e + 1) (n + 1))
  | e, 1 => sampleIJ (pS (L.pA + e)) (e / L.k) (e % L.k)
  | _, 0 => .block []

/-- The `k²` entries of `Â`. -/
def samples (c : Callee4) : Prog isa := L.ents c 0 (L.k * L.k)

end Kem

/-- `f[0] ×_T g[0] + ⋯ + f[n - 1] ×_T g[n - 1]` to polynomial 15 (with 16
for the products), accumulated left to right. -/
def dotN (A : Arith) (f g : Nat → Ptr) : Nat → Prog isa
  | 0 => .block []
  | 1 => mulAt A (pS 15) (f 0) (g 0)
  | n + 2 => .seq (dotN A f g (n + 1)) (.seq (mulAt A (pS 16) (f (n + 1)) (g (n + 1))) (addAt (pS 15) (pS 16)))

/-- ML-KEM-768: `k = 3`, `d_u = 10`, `d_v = 4`; 28 polynomials in `scratch`:
`Â` in polynomials 6–14, the working space from 17, the outputs of `PRF₂`
in 20, and the ciphertext (1088 bytes) in 26 and 27. -/
def kem768 : Kem where
  p := Spec.MlKem.mlKem768
  scr := 32768
  pA := 6
  pW := 17
  pPR := 20
  pCT := 26
  ceN := "vg_mlkem_compress_encode"
  ce := compressEncode
  ddN := "vg_mlkem_decode_decompress"
  dd := decodeDecompress

end VG.Impl.MlKem.X86_64
