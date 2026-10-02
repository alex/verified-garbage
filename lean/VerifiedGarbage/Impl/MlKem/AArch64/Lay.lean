import VerifiedGarbage.Impl.MlKem.AArch64.Top
import VerifiedGarbage.Impl.MlKem.AArch64.Compress

/-!
# ML-KEM on AArch64: what a parameter set's top-level functions depend on

`vg_mlkem768_*` and `vg_mlkem1024_*` are the same code for different
parameters (`KemLay`): `k`, the widths `d_u` and `d_v` of the ciphertext,
the size of `scratch`, and the functions that compress and encode, and
decode and decompress, at those widths. The buffers in `scratch`
(`KG`, `KEM`) follow from `k` and the ciphertext's length, and the code
unrolls its loops over `k` with `seqs`.
-/

namespace VG.Impl.MlKem.AArch64

open VG.AArch64

/-- `c₁; c₂; …; cₙ`, nested to the right (one program for one element). -/
def seqs : List (Prog isa) → Prog isa
  | [] => .block []
  | [c] => c
  | c :: cs => .seq c (seqs cs)

/-- A parameter set of ML-KEM on AArch64. -/
structure KemLay where
  /-- The rank of the module (FIPS 203 Table 2). -/
  k : Nat
  /-- The width of `u`'s coefficients in the ciphertext. -/
  du : Nat
  /-- The width of `v`'s coefficients in the ciphertext. -/
  dv : Nat
  /-- The size of `scratch`, in bytes. -/
  scl : Nat
  /-- The function compressing and encoding at the widths `du` and `dv`. -/
  ceName : String
  ce : Prog isa
  /-- The function decoding and decompressing at the widths `du` and `dv`. -/
  ddName : String
  dd : Prog isa

/-- `f ← f + g`, for polynomials at offsets of `scratch`. -/
def addAt (f g : Nat) : Prog isa :=
  .seq (.block (ptrTo .x0 .x28 f ++ ptrTo .x1 .x28 g)) (.call "vg_mlkem_add" add)

/-- A sum of `n` products into the polynomial at `tp`: the first product
(`term 0 tp`) into `tp`, and each other (`term j pp`) into `pp` and added
to `tp`. -/
def dotSteps (tp pp : Nat) (term : Nat → Nat → List (Prog isa)) : Nat → List (Prog isa)
  | 0 => []
  | 1 => term 0 tp
  | n + 2 => dotSteps tp pp term (n + 1) ++ term (n + 1) pp ++ [addAt tp pp]

namespace KemLay

/-- The length of a ciphertext, `32 (d_u k + d_v)` bytes. -/
abbrev ctLen (L : KemLay) : Nat := 32 * (L.du * L.k + L.dv)

/-- The length of an encapsulation key, `384 k + 32` bytes. -/
abbrev ekLen (L : KemLay) : Nat := 384 * L.k + 32

/-- The length of a decapsulation key, `768 k + 96` bytes. -/
abbrev dkLen (L : KemLay) : Nat := 768 * L.k + 96

end KemLay

/-- ML-KEM-768: `k = 3`, `d_u = 10`, `d_v = 4`, 32 KiB of `scratch`. -/
def lay768 : KemLay where
  k := 3
  du := 10
  dv := 4
  scl := 32768
  ceName := "vg_mlkem_compress_encode"
  ce := compressEncode
  ddName := "vg_mlkem_decode_decompress"
  dd := decodeDecompress

end VG.Impl.MlKem.AArch64
