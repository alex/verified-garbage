import VerifiedGarbage.Impl.MlKem.AArch64.Compress

/-!
# ML-KEM on AArch64: the NTT, its inverse and `MultiplyNTTs`

Products of two coefficients (less than `q² < 2³²`), and the sums of two of
them in `MultiplyNTTs` (less than `2q²`), are reduced by a Barrett
reduction with one 64-bit product (`barrett`): `x - ⌊x · 1290167 / 2³²⌋ · q`
is less than `2q` and congruent to `x`, and one conditional subtraction
(`csub`) finishes it. `x9 = q` and `x10 = 1290167` throughout.

The tables of `ζ^BitRev7(k)` (`zetas`) and of the `γᵢ` of `MultiplyNTTs`
(`gammas`) are stored in `scratch` first, as 128 `u32`s (`table`), and read
in order through a pointer.

* `ntt(f = x0, scratch = x1)`: the seven layers of Algorithm 9 as three
  nested loops: `x11 = len` (from 128, halved), `x13` the blocks of the
  layer (from 1, doubled), `x14` the layers left; for each block, its zeta
  (`x17`, the next of the table from `zetas[1]`, through `x12`), and `len`
  butterflies on `x2 = f + 4j` and `x3 = f + 4(j + len)`.
* `nttInv(f = x0, scratch = x1)`: the same for Algorithm 10, `len` from 2
  (doubled), the zetas from `zetas[127]` down, the inverse butterflies; then
  every coefficient times 3303.
* `multiplyNTTs(h = x0, f = x1, g = x2, scratch = x3)`: for each pair,
  `h[2i] = f[2i] g[2i] + (f[2i+1] g[2i+1] mod q) γᵢ` and
  `h[2i+1] = f[2i] g[2i+1] + f[2i+1] g[2i]`, each reduced.

Every address and branch depends only on the pointers.
-/

namespace VG.Impl.MlKem.AArch64

open VG.AArch64

/-- `ζ^BitRev7(k) mod q` for `k < 128` (FIPS 203 Appendix A); the proofs check
that it is (`VG.Proof.MlKem.zetas`). -/
def zetaTable : List Nat := [
  1, 1729, 2580, 3289, 2642, 630, 1897, 848, 1062, 1919, 193, 797, 2786, 3260, 569, 1746, 296,
  2447, 1339, 1476, 3046, 56, 2240, 1333, 1426, 2094, 535, 2882, 2393, 2879, 1974, 821, 289, 331,
  3253, 1756, 1197, 2304, 2277, 2055, 650, 1977, 2513, 632, 2865, 33, 1320, 1915, 2319, 1435,
  807, 452, 1438, 2868, 1534, 2402, 2647, 2617, 1481, 648, 2474, 3110, 1227, 910, 17, 2761, 583,
  2649, 1637, 723, 2288, 1100, 1409, 2662, 3281, 233, 756, 2156, 3015, 3050, 1703, 1651, 2789,
  1789, 1847, 952, 1461, 2687, 939, 2308, 2437, 2388, 733, 2337, 268, 641, 1584, 2298, 2037,
  3220, 375, 2549, 2090, 1645, 1063, 319, 2773, 757, 2099, 561, 2466, 2594, 2804, 1092, 403,
  1026, 1143, 2150, 2775, 886, 1722, 1212, 1874, 1029, 2110, 2935, 885, 2154]

/-- `ζ^(2BitRev7(i) + 1) mod q` for `i < 128` (FIPS 203 Appendix A); the proofs
check that it is (`VG.Proof.MlKem.gammas`). -/
def gammaTable : List Nat := [
  17, 3312, 2761, 568, 583, 2746, 2649, 680, 1637, 1692, 723, 2606, 2288, 1041, 1100, 2229, 1409,
  1920, 2662, 667, 3281, 48, 233, 3096, 756, 2573, 2156, 1173, 3015, 314, 3050, 279, 1703, 1626,
  1651, 1678, 2789, 540, 1789, 1540, 1847, 1482, 952, 2377, 1461, 1868, 2687, 642, 939, 2390,
  2308, 1021, 2437, 892, 2388, 941, 733, 2596, 2337, 992, 268, 3061, 641, 2688, 1584, 1745, 2298,
  1031, 2037, 1292, 3220, 109, 375, 2954, 2549, 780, 2090, 1239, 1645, 1684, 1063, 2266, 319,
  3010, 2773, 556, 757, 2572, 2099, 1230, 561, 2768, 2466, 863, 2594, 735, 2804, 525, 1092, 2237,
  403, 2926, 1026, 2303, 1143, 2186, 2150, 1179, 2775, 554, 886, 2443, 1722, 1607, 1212, 2117,
  1874, 1455, 1029, 2300, 2110, 1219, 2935, 394, 885, 2444, 2154, 1175]

/-- `d ← d - ⌊d · C / 2³²⌋ · q`, with `C = 1290167` in `cr`, `q` in `qr`, and
a temporary `t`. -/
def barrett (d t cr qr : Reg) : List Instr :=
  [.mul .x t d cr, .lsr .x t t 32, .mul .x t t qr, .sub .x d d t]

/-- The 128 entries of `T` as `u32`s at `[b]`, through `x9`. -/
def table (T : List Nat) (b : Reg) : List Instr :=
  (List.range 128).flatMap fun k =>
    [.movz .x .x9 (BitVec.ofNat 16 (T.getD k 0)) 0, .str .w .x9 b (4 * k)]

/-- `q` in `x9`, `1290167` in `x10`. -/
def consts : List Instr := .movz .x .x9 3329 0 :: movImm .x10 1290167

/-! ## `ntt` -/

/-- The butterfly on `[x2]` and `[x3]` with the zeta `x17`. -/
def bflyBody : List Instr :=
  [.ldr .w .x6 .x2 0, .ldr .w .x7 .x3 0, .mul .x .x7 .x7 .x17] ++ barrett .x7 .x8 .x10 .x9 ++
  csub .x7 .x8 .x9 ++ (.add .x .x8 .x6 .x7 :: csub .x8 .x4 .x9 : List Instr) ++
  ([.str .w .x8 .x2 0, .add .x .x6 .x6 .x9, .sub .x .x6 .x6 .x7] : List Instr) ++ csub .x6 .x4 .x9 ++
  ([.str .w .x6 .x3 0, .addImm .x .x2 .x2 4, .addImm .x .x3 .x3 4, .subImm .x .x5 .x5 1] : List Instr)

/-- A block: its zeta, then `len` butterflies. -/
def nttBlockCode : Prog isa :=
  .seq (.block [.ldr .w .x17 .x12 0, .addImm .x .x12 .x12 4, .add .x .x3 .x2 .x15, mov .x5 .x11]) <|
  .seq (.loop (.block bflyBody) (.nonzero .x .x5))
    (.block [mov .x2 .x3, .subImm .x .x16 .x16 1])

/-- A layer: its blocks. -/
def nttLayerCode : Prog isa :=
  .seq (.block [mov .x2 .x0, mov .x16 .x13, .lsl .x .x15 .x11 2]) <|
  .seq (.loop nttBlockCode (.nonzero .x .x16))
    (.block [.lsr .x .x11 .x11 1, .add .x .x13 .x13 .x13, .subImm .x .x14 .x14 1])

def ntt : Prog isa :=
  .seq (.block (table zetaTable .x1 ++ consts ++
    ([.movz .x .x11 128 0, .addImm .x .x12 .x1 4, .movz .x .x13 1 0, .movz .x .x14 7 0] :
      List Instr)))
    (.loop nttLayerCode (.nonzero .x .x14))

/-! ## `nttInv` -/

/-- The inverse butterfly on `[x2]` and `[x3]` with the zeta `x17`. -/
def ibflyBody : List Instr :=
  [.ldr .w .x6 .x2 0, .ldr .w .x7 .x3 0, .add .x .x8 .x6 .x7] ++ csub .x8 .x4 .x9 ++
  ([.str .w .x8 .x2 0, .add .x .x7 .x7 .x9, .sub .x .x7 .x7 .x6] : List Instr) ++ csub .x7 .x4 .x9 ++
  (.mul .x .x7 .x7 .x17 :: barrett .x7 .x8 .x10 .x9 : List Instr) ++ csub .x7 .x8 .x9 ++
  ([.str .w .x7 .x3 0, .addImm .x .x2 .x2 4, .addImm .x .x3 .x3 4, .subImm .x .x5 .x5 1] : List Instr)

/-- A block: its zeta, then `len` inverse butterflies. -/
def nttInvBlockCode : Prog isa :=
  .seq (.block [.ldr .w .x17 .x12 0, .subImm .x .x12 .x12 4, .add .x .x3 .x2 .x15, mov .x5 .x11]) <|
  .seq (.loop (.block ibflyBody) (.nonzero .x .x5))
    (.block [mov .x2 .x3, .subImm .x .x16 .x16 1])

/-- A layer: its blocks. -/
def nttInvLayerCode : Prog isa :=
  .seq (.block [mov .x2 .x0, mov .x16 .x13, .lsl .x .x15 .x11 2]) <|
  .seq (.loop nttInvBlockCode (.nonzero .x .x16))
    (.block [.lsl .x .x11 .x11 1, .lsr .x .x13 .x13 1, .subImm .x .x14 .x14 1])

/-- `[x2] ← [x2] · x17 mod q`, and on to the next coefficient. -/
def scaleBody : List Instr :=
  [.ldr .w .x6 .x2 0, .mul .x .x6 .x6 .x17] ++ barrett .x6 .x8 .x10 .x9 ++ csub .x6 .x8 .x9 ++
  ([.str .w .x6 .x2 0, .addImm .x .x2 .x2 4, .subImm .x .x5 .x5 1] : List Instr)

def nttInv : Prog isa :=
  .seq (.block (table zetaTable .x1 ++ consts ++
    ([.movz .x .x11 2 0, .addImm .x .x12 .x1 508, .movz .x .x13 64 0, .movz .x .x14 7 0] :
      List Instr))) <|
  .seq (.loop nttInvLayerCode (.nonzero .x .x14)) <|
  .seq (.block [.movz .x .x17 3303 0, mov .x2 .x0, .movz .x .x5 256 0])
    (.loop (.block scaleBody) (.nonzero .x .x5))

/-! ## `multiplyNTTs` -/

/-- The pair `i`: `x6 = f[2i]`, `x7 = f[2i+1]`, `x12 = g[2i]`, `x13 = g[2i+1]`,
`x14 = γᵢ`. -/
def mulBody : List Instr :=
  [.ldr .w .x6 .x1 0, .ldr .w .x7 .x1 4, .ldr .w .x12 .x2 0, .ldr .w .x13 .x2 4, .ldr .w .x14 .x3 0,
    .mul .x .x15 .x7 .x13] ++ barrett .x15 .x8 .x10 .x9 ++ csub .x15 .x8 .x9 ++
  ([.mul .x .x15 .x15 .x14, .madd .x .x15 .x6 .x12 .x15] : List Instr) ++
  barrett .x15 .x8 .x10 .x9 ++ csub .x15 .x8 .x9 ++
  ([.str .w .x15 .x0 0, .mul .x .x15 .x6 .x13, .madd .x .x15 .x7 .x12 .x15] : List Instr) ++
  barrett .x15 .x8 .x10 .x9 ++ csub .x15 .x8 .x9 ++
  ([.str .w .x15 .x0 4, .addImm .x .x0 .x0 8, .addImm .x .x1 .x1 8, .addImm .x .x2 .x2 8,
    .addImm .x .x3 .x3 4, .subImm .x .x11 .x11 1] : List Instr)

def multiplyNTTs : Prog isa :=
  .seq (.block (table gammaTable .x3 ++ consts ++ ([.movz .x .x11 128 0] : List Instr)))
    (.loop (.block mulBody) (.nonzero .x .x11))

end VG.Impl.MlKem.AArch64
