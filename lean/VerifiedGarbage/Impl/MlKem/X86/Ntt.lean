import VerifiedGarbage.Impl.MlKem.X86.Basic

/-!
# ML-KEM on x86 (32-bit): the NTT, its inverse and `MultiplyNTTs`

Products of two coefficients (less than `q² < 2³²`), and the sums of two of
them in `MultiplyNTTs` (less than `2q²`), are reduced with a Barrett
reduction whose quotient is the high half of a `mul` (`red`):
`x - ⌊x · 1290167 / 2³²⌋ · q` is less than `2q` and congruent to `x`, and one
conditional subtraction (`csub`) finishes it.

The tables of `ζ^BitRev7(k)` (`zetaTable`) and of the `γᵢ` of `MultiplyNTTs`
(`gammaTable`) are stored in `scratch` first, as 128 `u32`s (`table`), and
read through a pointer in `ebp`. All seven registers are busy in a
butterfly, so the loops over blocks compare their pointer with the end of
the polynomial, which is stored in the argument slot of `scratch` once the
table is written.

* `ntt(f, scratch)`: the seven layers of Algorithm 9, one after the other
  (`layerCode bflyBody zUp len`, for `len` from 128 down to 2): `esi = f + 4j`,
  `edi = f + 4(j + len)`, `ebp` at the zeta of the block (from `zetas[1]`
  up), `ecx` the butterflies left in the block; each butterfly computes
  `t = ζ · f[j + len] mod q` in `ebx`.
* `nttInv(f, scratch)`: the same for Algorithm 10 (`len` from 2 up, the zetas
  from `zetas[127]` down, the inverse butterflies), then every coefficient
  times 3303.
* `multiplyNTTs(h, f, g, scratch)`: for each pair, with `ebx = h + 8i`,
  `esi = f + 8i`, `edi = g + 8i` and `ebp` at `γᵢ`:
  `h[2i] = f[2i] g[2i] + (f[2i+1] g[2i+1] mod q) γᵢ` and
  `h[2i+1] = f[2i] g[2i+1] + f[2i+1] g[2i]`, each reduced, accumulated in `ecx`.

Every address and branch depends only on the pointers.
-/

namespace VG.Impl.MlKem.X86

open VG.X86

/-- `++`, grouping to the right. -/
local infixr:65 " +++ " => HAppend.hAppend

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

/-- The 128 entries of `T` as `u32`s at `[b]`, through `edx`. -/
def table (T : List Nat) (b : Reg) : List Instr :=
  (List.range 128).flatMap fun k => [.mov .edx (.imm (BitVec.ofNat 32 (T.getD k 0))), .store (at_ b (4 * k)) .edx]

/-- `r ← (x mod q)` from `eax = r = x < 2³²`, with `edx` as a temporary:
`x - ⌊x · 1290167 / 2³²⌋ · q`, then `csub`. -/
def red (r : Reg) : List Instr :=
  [.mov .edx (.imm 1290167), .mul .edx, .mov .eax (.imm 3329), .mul .edx, .alu .sub r (.reg .eax)] +++
    csub r .edx

/-! ## `ntt` -/

/-- The butterfly on `[esi]` and `[edi]` with the zeta at `[ebp]`. -/
def bflyBody : List Instr :=
  [.mov .eax (.mem (at_ .edi 0)), .mov .edx (.mem (at_ .ebp 0)), .mul .edx, .mov .ebx (.reg .eax)] +++
  red .ebx +++
  [.mov .eax (.mem (at_ .esi 0)), .alu .add .eax (.imm Q), .alu .sub .eax (.reg .ebx)] +++ csub .eax .edx +++
  [.store (at_ .edi 0) .eax, .mov .eax (.mem (at_ .esi 0)), .alu .add .eax (.reg .ebx)] +++ csub .eax .edx +++
  [.store (at_ .esi 0) .eax, .alu .add .esi (.imm 4), .alu .add .edi (.imm 4), .alu .sub .ecx (.imm 1)]

/-- The first instructions of a block of the layer with `len`. -/
def blockInit (len : Nat) : List Instr :=
  [.mov .edi (.reg .esi), .alu .add .edi (.imm (BitVec.ofNat 32 (4 * len))),
    .mov .ecx (.imm (BitVec.ofNat 32 len))]

/-- The last instructions of a block: `ebp` moves to the next zeta (`dz`). -/
def blockEnd (dz : Instr) : List Instr := [.mov .esi (.reg .edi), dz, .alu .cmp .esi (.mem (at_ .esp 24))]

/-- A layer of butterflies `body`, `len` apart: its blocks. -/
def layerCode (body : List Instr) (dz : Instr) (len : Nat) : Prog isa :=
  .seq (.block [.mov .esi (.mem (at_ .esp 20))]) <|
  .loop (.seq (.block (blockInit len)) (.seq (.loop (.block body) .ne) (.block (blockEnd dz)))) .ne

/-- `ebp` to the next zeta, up. -/
def zUp : Instr := .alu .add .ebp (.imm 4)

/-- `ebp` to the next zeta, down. -/
def zDown : Instr := .alu .sub .ebp (.imm 4)

/-- The layers with the given `len`s. -/
def layers (code : Nat → Prog isa) : List Nat → Prog isa
  | [] => .block []
  | len :: lens => .seq (code len) (layers code lens)

/-- `eax = scratch`. -/
def ldScratch : List Instr := [.mov .eax (.mem (at_ .esp 24))]

/-- The zeta table, `ebp` at `zetas[z]`, and `f + 1024` in the slot of `scratch`. -/
def nttSetup (z : Nat) : List Instr :=
  table zetaTable .eax +++
  [.mov .ebp (.reg .eax), .alu .add .ebp (.imm (BitVec.ofNat 32 (4 * z))), .mov .edx (.mem (at_ .esp 20)),
    .alu .add .edx (.imm 1024), .store (at_ .esp 24) .edx]

def ntt : Prog isa :=
  leaf (.seq (.block ldScratch) (.seq (.block (nttSetup 1)) (layers (layerCode bflyBody zUp) [128, 64, 32, 16, 8, 4, 2])))

/-! ## `nttInv` -/

/-- The inverse butterfly on `[esi]` and `[edi]` with the zeta at `[ebp]`. -/
def ibflyBody : List Instr :=
  [.mov .ebx (.mem (at_ .edi 0)), .alu .add .ebx (.imm Q), .alu .sub .ebx (.mem (at_ .esi 0)),
    .mov .eax (.mem (at_ .esi 0)), .alu .add .eax (.mem (at_ .edi 0))] +++ csub .eax .edx +++
  [.store (at_ .esi 0) .eax, .mov .eax (.reg .ebx), .mov .edx (.mem (at_ .ebp 0)), .mul .edx,
    .mov .ebx (.reg .eax)] +++ red .ebx +++
  [.store (at_ .edi 0) .ebx, .alu .add .esi (.imm 4), .alu .add .edi (.imm 4), .alu .sub .ecx (.imm 1)]

/-- `[esi] ← [esi] · 3303 mod q`, and on to the next coefficient. -/
def scaleBody : List Instr :=
  [.mov .eax (.mem (at_ .esi 0)), .mov .edx (.imm 3303), .mul .edx, .mov .ebx (.reg .eax)] +++ red .ebx +++
  [.store (at_ .esi 0) .ebx, .alu .add .esi (.imm 4), .alu .sub .ecx (.imm 1)]

def nttInv : Prog isa :=
  leaf (.seq (.block ldScratch) (.seq (.block (nttSetup 127))
    (.seq (layers (layerCode ibflyBody zDown) [2, 4, 8, 16, 32, 64, 128])
      (.seq (.block [.mov .esi (.mem (at_ .esp 20))])
        (.seq (.block [.mov .ecx (.imm 256)]) (.loop (.block scaleBody) .ne))))))

/-! ## `multiplyNTTs` -/

/-- The pair `i`: `h[2i]` and `h[2i + 1]`. -/
def mulBody : List Instr :=
  [.mov .eax (.mem (at_ .esi 4)), .mov .edx (.mem (at_ .edi 4)), .mul .edx, .mov .ecx (.reg .eax)] +++
  red .ecx +++
  [.mov .eax (.reg .ecx), .mov .edx (.mem (at_ .ebp 0)), .mul .edx, .mov .ecx (.reg .eax),
    .mov .eax (.mem (at_ .esi 0)), .mov .edx (.mem (at_ .edi 0)), .mul .edx, .alu .add .ecx (.reg .eax),
    .mov .eax (.reg .ecx)] +++ red .ecx +++
  [.store (at_ .ebx 0) .ecx, .mov .eax (.mem (at_ .esi 0)), .mov .edx (.mem (at_ .edi 4)), .mul .edx,
    .mov .ecx (.reg .eax), .mov .eax (.mem (at_ .esi 4)), .mov .edx (.mem (at_ .edi 0)), .mul .edx,
    .alu .add .ecx (.reg .eax), .mov .eax (.reg .ecx)] +++ red .ecx +++
  [.store (at_ .ebx 4) .ecx, .alu .add .ebx (.imm 8), .alu .add .esi (.imm 8), .alu .add .edi (.imm 8),
    .alu .add .ebp (.imm 4), .alu .cmp .ebx (.mem (at_ .esp 32))]

/-- `eax = scratch`. -/
def mulLd : List Instr := [.mov .eax (.mem (at_ .esp 32))]

/-- The gamma table, `ebp = scratch`, `h + 1024` in the slot of `scratch`, and the pointers. -/
def mulSetup : List Instr :=
  table gammaTable .eax +++
  [.mov .ebp (.reg .eax), .mov .ebx (.mem (at_ .esp 20)), .mov .edx (.reg .ebx), .alu .add .edx (.imm 1024),
    .store (at_ .esp 32) .edx, .mov .esi (.mem (at_ .esp 24)), .mov .edi (.mem (at_ .esp 28))]

def multiplyNTTs : Prog isa :=
  leaf (.seq (.block mulLd) (.seq (.block mulSetup) (.loop (.block mulBody) .ne)))

end VG.Impl.MlKem.X86
