import VerifiedGarbage.Impl.X25519.X86_64.Ifma

/-!
# Ed25519: doublings with AVX512_IFMA

`Ifma.double4` doubles the point in slots 0–3 four times, as `double4` does,
with the four coordinates `(X, Y, Z, T)` in the four quadwords (lanes) of
`ymm` registers and X25519's four-lane field arithmetic
(`Impl/X25519/X86_64/Ifma.lean`): five limbs of 51 bits, `mul4`'s
products with AVX512_IFMA's `vpmadd52luq` and `vpmadd52huq`, and `carry`.

* `vload` splits the words of slots 0–3 into the limbs of the lanes of
  `ymm0–ymm4`: the four rows transposed (`vpunpck{l,h}qdq`, `vperm2i128`),
  then shifted and masked as `vinit` splits `x₁`.
* A doubling (`vdbl`) is `dbl-2008-hwcd` (`dblOps`) in two products: first
  `(X, Y, Z, X) · (X, Y, Z, Y) = (A, B, C', P) = (X², Y², Z², XY)`; then,
  with `q = (A + B, A + B, 2C', 2P)` and `r = (A - B, B - A, …)` (each
  difference plus the bias `2¹¹ p`), `E = 2P`, `G = B - A`,
  `F = 2C' + (A - B)` and `H = A + B`, `(E, G, F, E) · (F, H, G, H) =
  (EF, GH, FG, EH)`, the doubled point with its `T`.
* `vstore` carries the lanes and puts them back into slots 0–3, as
  X25519's `vpack` does.

The constants are X25519's (`KM`, `K19`, `KB0`, `KB1`) and the masks of
`vstore` (`EK13`, `EK26`, `EK39`), all below byte 1888 of the scratch, as
are the operands' slots `OPL` and `OPV`. Verification's inputs are public, so
the products need not run between Intel's MXCSR prologue and epilogue (see
"MCDT" in `TCB/X86_64/Isa.lean`). Every address is the scratch plus a
constant, and the only branch is on the loop counter.
-/

namespace VG.Impl.Ed25519.X86_64.Ifma

open VG.X86_64
open VG.Impl.X25519.X86_64 (sc)
open VG.Impl.X25519.X86_64.Ifma (y ld st v srl sll perm blend zero lanes ord carry mul4 kb bcast
  KM K19 KB0 KB1 OPL OPV)

/-- `2¹³ - 1`, `2²⁶ - 1` and `2³⁹ - 1` in each quadword (`vstore`). -/
def EK13 : Nat := 1792
def EK26 : Nat := 1824
def EK39 : Nat := 1856

/-- The constants into the scratch, from the registers `VG.Impl.X25519.X86_64.Ifma.consts`
sets, and the limbs of slots 0–3 (words `w₀–w₃` of each) into the lanes of
`ymm0–ymm4`: `w₀ mod 2⁵¹`, `w₀ >> 51 | (w₁ mod 2³⁸) << 13`, …, `w₃ >> 12`. -/
def vload : List Instr :=
  bcast 9 .rax ++ [st KM 9] ++ bcast 10 .rcx ++ [st K19 10] ++ bcast 10 .rdx ++ [st KB0 10] ++
  bcast 10 .rbp ++ [st KB1 10] ++ bcast 10 .r8 ++ [st EK13 10] ++ bcast 10 .r9 ++ [st EK26 10] ++
  bcast 10 .r10 ++ [st EK39 10] ++
  [ld 11 64, ld 12 96, ld 13 128, ld 14 160,
    v .vpunpcklqdq 0 11 12, v .vpunpckhqdq 1 11 12, v .vpunpcklqdq 2 13 14, v .vpunpckhqdq 3 13 14,
    .vop (.vperm2i128 (y 5) (y 0) (y 2) 0x20), .vop (.vperm2i128 (y 6) (y 1) (y 3) 0x20),
    .vop (.vperm2i128 (y 7) (y 0) (y 2) 0x31), .vop (.vperm2i128 (y 8) (y 1) (y 3) 0x31),
    v .vpand 0 5 9,
    srl 1 5 51, srl 11 9 13, v .vpand 11 6 11, sll 11 11 13, v .vpor 1 1 11,
    srl 2 6 38, srl 11 9 26, v .vpand 11 7 11, sll 11 11 26, v .vpor 2 2 11,
    srl 3 7 25, srl 11 9 39, v .vpand 11 8 11, sll 11 11 39, v .vpor 3 3 11,
    srl 4 8 12]

/-- `(X, Y, Z, X)` to `OPL` and `(X, Y, Z, Y)` into `ymm5–ymm9`. -/
def dblA : List Instr :=
  (List.range 5).flatMap fun j => [perm 10 j (ord 0 1 2 0), st (OPL + 32 * j) 10, perm (5 + j) j (ord 0 1 2 1)]

/-- From `(A, B, C', P)` in `ymm0–ymm4`: `(E, G, F, E)` into `ymm0–ymm4` and
`(F, H, G, H)` into `ymm5–ymm9`, neither carried, through
`q = (A + B, A + B, 2C', 2P)` (`ymm11`) and `r = (A - B, B - A, …)` (`ymm12`). -/
def dblB : List Instr :=
  (List.range 5).flatMap fun j =>
    [perm 10 j (ord 1 0 2 3), v .vpaddq 11 j 10, ld 12 (kb j), v .vpaddq 12 12 j, v .vpsubq 12 12 10,
      perm 13 12 (ord 0 0 0 0), perm 10 11 (ord 2 2 2 2), v .vpaddq 10 10 13,
      perm 13 11 (ord 3 3 3 3), blend 13 13 12 (lanes false true false false),
      blend j 13 10 (lanes false false true false),
      perm 13 12 (ord 1 1 1 1), perm 11 11 (ord 0 0 0 0), blend 10 10 11 (lanes false true false true),
      blend (5 + j) 10 13 (lanes false false true false)]

/-- `(E, G, F, E)` to `OPV`. -/
def dblC : List Instr := (List.range 5).flatMap fun j => [st (OPV + 32 * j) j]

/-- A doubling of the point in the lanes of `ymm0–ymm4`, with its `T`. The first product's
limbs are not carried: they are small enough (below `2⁶⁰ + 2⁵⁶`) for `dblB`'s sums. -/
def vdbl : List Instr :=
  carry id ++ dblA ++ mul4 OPL ++ dblB ++ carry (5 + ·) ++ carry id ++ dblC ++ mul4 OPV

/-- The lanes of `ymm0–ymm4`, carried as by `vfinish`, into slots 0–3. -/
def vstore : List Instr :=
  carry id ++ carry id ++ [ld 10 KM] ++
  ([0, 1, 2, 3].flatMap fun k =>
    [srl 11 k 51, v .vpand k k 10, v .vpaddq (k + 1) (k + 1) 11]) ++
  [ld 11 EK13, v .vpand 12 1 11, sll 12 12 51, v .vpor 5 0 12,
    srl 6 1 13, ld 11 EK26, v .vpand 12 2 11, sll 12 12 38, v .vpor 6 6 12,
    srl 7 2 26, ld 11 EK39, v .vpand 12 3 11, sll 12 12 25, v .vpor 7 7 12,
    srl 8 3 39, sll 12 4 12, v .vpor 8 8 12,
    v .vpunpcklqdq 0 5 6, v .vpunpckhqdq 1 5 6, v .vpunpcklqdq 2 7 8, v .vpunpckhqdq 3 7 8,
    .vop (.vperm2i128 (y 5) (y 0) (y 2) 0x20), .vop (.vperm2i128 (y 6) (y 1) (y 3) 0x20),
    .vop (.vperm2i128 (y 7) (y 0) (y 2) 0x31), .vop (.vperm2i128 (y 8) (y 1) (y 3) 0x31),
    st 64 5, st 96 6, st 128 7, st 160 8, .vop .vzeroupper]

/-- Four doublings of slots 0–3, in the lanes, counted by `rsi`. -/
def double4 : Prog isa :=
  .seq (.block (VG.Impl.X25519.X86_64.Ifma.consts ++ vload ++ [.mov32 .rsi (.imm 4)]))
    (.seq (.loop (.block (vdbl ++ [.alu .sub .rsi (.imm 1)])) .ne) (.block vstore))

end VG.Impl.Ed25519.X86_64.Ifma
