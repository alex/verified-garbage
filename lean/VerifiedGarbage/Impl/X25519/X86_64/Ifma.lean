import VerifiedGarbage.Impl.X25519.X86_64.Adx

/-!
# X25519: x86-64 implementation with AVX512_IFMA

`vg_x25519_ifma`: the code of `vg_x25519_adx` (`X86_64/Adx.lean`) with
another ladder, which runs the four field multiplications of each of its
three stages at once, one to each quadword of `ymm` registers, with
AVX512_IFMA's `vpmadd52luq` and `vpmadd52huq` (on `ymm` registers, with
AVX512VL): each multiplies the low 52 bits of two quadwords and adds the low
(`luq`) or high (`huq`) 52 bits of the 104-bit product to a third.

* A field element is five limbs `x₀ + 2⁵¹ x₁ + … + 2²⁰⁴ x₄`, standing for
  its residue modulo `p`, and four of them are five `ymm` registers (limb
  `i` of lane `l` in quadword `l` of register `i`), or five 32-byte slots of
  the working space.
* `mul4`: the lanes of five registers times those of a slot, lane by lane.
  Each product `a_i b_j` of two limbs below `2⁵²` is `lo + 2⁵² hi`, so
  `lo` goes to column `i + j` and `2 hi` to column `i + j + 1`; column `c ≥
  5` is folded into `c - 5` as 19 times itself (`2²⁵⁵ ≡ 19`). The result is
  five limbs below `2⁶¹`, not carried.
* `carry`: each limb keeps its low 51 bits and passes the rest to the next,
  the last one's times 19 to the first (with `vpmadd52luq`), all at once:
  limbs below `2⁶³` become limbs below `2⁵²`, which `vpmadd52luq` and
  `vpmadd52huq` read in full.
* A difference `x - y` is `x + 2¹¹ p - y` (`bias`), limb by limb, which
  never goes negative for limbs `y` below `2⁶¹`.

An iteration of the ladder (`vstep`), with `(x₂, z₂, x₃, z₃)` in the lanes of
`ymm0–ymm4` (in the lanes 0–3), swaps the pairs `(x₂, z₂)`, `(x₃, z₃)` with
the mask `-swap` (as RFC 7748 §5 describes), then:

1. `(A, B, C, D) = (x₂ + z₂, x₂ - z₂, x₃ + z₃, x₃ - z₃)`, carried, and
   multiplied lane by lane: `(A, B, D, C) · (A, B, A, B) = (AA, BB, DA, CB)`;
2. `(DA + CB, DA - CB, AA, E = AA - BB) · (DA + CB, DA - CB, BB, a24) =
   (x₃', t, x₂', a24 E)`;
3. `(x₂', E, x₃', t) · (1, AA + a24 E, 1, x₁) = (x₂', z₂', x₃', z₃')`.

The first operand of each product is in the slot `OPL`, `OPV` or `OPG`, the
second in `ymm5–ymm9`, and the constants (`KM`, `K19`, …) are in the working
space.

Before the loop `vsetup` sets the constants, splits `x₁` into limbs and sets
the lanes; after it `vfinish` carries the lanes and puts each back into four
64-bit words (in the slots `x2, z2, x3, z3`, which `vg_x25519`'s code reads
next). `vpmadd52luq` and `vpmadd52huq` have MXCSR-configuration-dependent
timing on some processors, so the loop and `vfinish` run between Intel's
prologue and epilogue (`withMxcsr`; see "MCDT" in `TCB/X86_64/Isa.lean`).

The only branches are on the loop counter, and every address is the working
space plus a constant or a counter, so only the pointers can affect timing.
-/

namespace VG.Impl.X25519.X86_64

open VG.X86_64

namespace Ifma

/-! ## The layout of the working space beyond `BITS` -/

/-- The first operands of the products. -/
def OPL : Nat := 1024
def OPV : Nat := 1184
def OPG : Nat := 1344
/-- `2⁵¹ - 1` in each quadword. -/
def KM : Nat := 1664
/-- 19 in each quadword. -/
def K19 : Nat := 1696
/-- The limbs of `bias = 2¹¹ p`, limb 0 and the others, in each quadword. -/
def KB0 : Nat := 1728
def KB1 : Nat := 1760
/-- `(0, 0, 0, a24)`, five limbs. -/
def KA24 : Nat := 1792
/-- `(1, 0, 1, x₁)`, five limbs. -/
def KX1 : Nat := 1952
/-- `2¹³ - 1`, `2²⁶ - 1` and `2³⁹ - 1` in each quadword (`vfinish`). -/
def K13 : Nat := 2112
def K26 : Nat := 2144
def K39 : Nat := 2176
/-- MXCSR, saved, and `0x1FBF` (`withMxcsr`). -/
def MX : Nat := 2208

/-- `ymm i`. -/
def y : Nat → XReg
  | 0 => .xmm0 | 1 => .xmm1 | 2 => .xmm2 | 3 => .xmm3
  | 4 => .xmm4 | 5 => .xmm5 | 6 => .xmm6 | 7 => .xmm7
  | 8 => .xmm8 | 9 => .xmm9 | 10 => .xmm10 | 11 => .xmm11
  | 12 => .xmm12 | 13 => .xmm13 | 14 => .xmm14 | _ => .xmm15

def ld (d : Nat) (o : Nat) : Instr := .vmovdquLoad .l256 (y d) (sc o)
def st (o : Nat) (r : Nat) : Instr := .vmovdquStore .l256 (sc o) (y r)
def v (op : VBinOp) (d a b : Nat) : Instr := .vop (.vbin op .l256 (y d) (y a) (y b))
def srl (d a : Nat) (n : BitVec 8) : Instr := .vop (.vshift .psrlq .l256 (y d) (y a) n)
def sll (d a : Nat) (n : BitVec 8) : Instr := .vop (.vshift .psllq .l256 (y d) (y a) n)
def perm (d a : Nat) (o : BitVec 8) : Instr := .vop (.vpermq (y d) (y a) o)
def blend (d a b : Nat) (sel : BitVec 8) : Instr := .vop (.vpblendd .l256 (y d) (y a) (y b) sel)
def lo (d a b : Nat) : Instr := .vop (.vpmadd52luq .l256 (y d) (y a) (y b))
def hi (d a b : Nat) : Instr := .vop (.vpmadd52huq .l256 (y d) (y a) (y b))
def zero (d : Nat) : Instr := v .vpxor d d d
def mov (d a : Nat) : Instr := .vop (.vmovdqa .l256 (y d) (y a))

/-- `vpblendd`'s selectors of the quadwords (lanes) `l`. -/
def lanes (l0 l1 l2 l3 : Bool) : BitVec 8 :=
  (if l0 then 0x03 else 0) ||| (if l1 then 0x0c else 0) ||| (if l2 then 0x30 else 0) |||
    (if l3 then 0xc0 else 0)

/-- `vpermq`'s order: lane `l` from lane `sₗ`. -/
def ord (s0 s1 s2 s3 : Nat) : BitVec 8 := BitVec.ofNat 8 (s0 + 4 * s1 + 16 * s2 + 64 * s3)

/-! ## Field arithmetic, four lanes at once -/

/-- The limbs `ymm r₀, …, ymm r₄` carried, with `ymm10–ymm12` as scratch:
from the top down, each limb's bits from 51 up (`c`) are added to the next,
which is already masked, and the top one's (`c₄`, in `ymm11`) times 19 to
the lowest. -/
def carry (r : Nat → Nat) : List Instr :=
  [ld 10 KM, srl 11 (r 4) 51, v .vpand (r 4) (r 4) 10] ++
  ([3, 2, 1, 0].flatMap fun k =>
    [srl 12 (r k) 51, v .vpand (r k) (r k) 10, v .vpaddq (r (k + 1)) (r (k + 1)) 12]) ++
  [ld 12 K19, lo (r 0) 11 12]

/-- The low half of `a_i b_j` with `i + j = c` into `acc` (`a_i` in
`ymm10`, `b` in `ymm5–ymm9`), if there is such a `j`. -/
def maddLo (acc i c : Nat) : List Instr :=
  if i ≤ c ∧ c - i < 5 then [lo acc 10 (5 + (c - i))] else []

/-- The high half of `a_i b_j` with `i + j + 1 = c` into `acc`, likewise. -/
def maddHi (acc i c : Nat) : List Instr :=
  if i + 1 ≤ c ∧ c - (i + 1) < 5 then [hi acc 10 (5 + (c - (i + 1)))] else []

/-- `ymm k = r_k`: column `k` plus 19 times column `k + 5` of `a · b`, `a`
from the slot `a`, `b` in `ymm5–ymm9`, with each column `c` (the low halves
of the products `a_i b_j` with `i + j = c`, and twice their high halves with
`i + j = c - 1`) accumulated in `ymm11` (low halves), `ymm12` (high), and for
`c + 5` in `ymm13`, `ymm14`. -/
def mulCol (a k : Nat) : List Instr :=
  [zero 11, zero 12, zero 13, zero 14] ++
  ((List.range 5).flatMap fun i =>
    [ld 10 (a + 32 * i)] ++ maddLo 11 i k ++ maddHi 12 i k ++ maddLo 13 i (k + 5) ++
      maddHi 14 i (k + 5)) ++
  [sll 12 12 1, v .vpaddq 11 11 12, sll 14 14 1, v .vpaddq 13 13 14, v .vpaddq 11 11 13,
    sll 12 13 1, v .vpaddq 11 11 12, sll 12 13 4, v .vpaddq k 11 12]

/-- `ymm0–ymm4 = [a] · ymm5–ymm9`, lane by lane, not carried; `ymm5–ymm9`
are kept. -/
def mul4 (a : Nat) : List Instr :=
  mulCol a 0 ++ mulCol a 1 ++ mulCol a 2 ++ mulCol a 3 ++ mulCol a 4

/-- The bias for limb `j`. -/
def kb (j : Nat) : Nat := if j = 0 then KB0 else KB1

/-! ## An iteration -/

/-- Swaps lanes 0, 1 with 2, 3 of `ymm0–ymm4` if the mask `ymm15` is all
ones. -/
def vswap : List Instr :=
  (List.range 5).flatMap fun j =>
    [perm 10 j (ord 2 3 0 1), v .vpxor 10 10 j, v .vpand 10 10 15, v .vpxor j j 10]

/-- `(A, B, C, D) = (x₂ + z₂, x₂ - z₂, x₃ + z₃, x₃ - z₃)` into `ymm0–ymm4`,
not carried. -/
def stage1a : List Instr :=
  (List.range 5).flatMap fun j =>
    [perm 10 j (ord 0 0 2 2), perm 11 j (ord 1 1 3 3), ld 12 (kb j), v .vpsubq 12 12 11,
      blend 11 11 12 (lanes false true false true), v .vpaddq j 10 11]

/-- `(A, B, D, C)` to `OPL` and `(A, B, A, B)` into `ymm5–ymm9`. -/
def stage1b : List Instr :=
  (List.range 5).flatMap fun j => [perm 10 j (ord 0 1 3 2), st (OPL + 32 * j) 10, perm (5 + j) j (ord 0 1 0 1)]

/-- Stage 1's operands, from `(x₂, z₂, x₃, z₃)` in `ymm0–ymm4`. -/
def stage1 : List Instr := stage1a ++ carry id ++ stage1b

/-- From `(AA, BB, DA, CB)` in `ymm0–ymm4`: `(DA + CB, DA - CB, AA, AA - BB)`
into `ymm5–ymm9` and `(DA + CB, DA - CB, BB, a24)` into `ymm0–ymm4` (with
`ymm13` zero), neither carried. -/
def stage2a : List Instr :=
  [zero 13] ++
  (List.range 5).flatMap fun j =>
    [perm 10 j (ord 2 2 0 0), perm 11 j (ord 3 3 1 1), ld 12 (kb j), v .vpsubq 12 12 11,
      blend 11 11 12 (lanes false true false true), blend 11 11 13 (lanes false false true false),
      v .vpaddq (5 + j) 10 11,
      perm 10 j (ord 0 0 1 0), blend j (5 + j) 10 (lanes false false true false),
      ld 11 (KA24 + 32 * j), blend j j 11 (lanes false false false true)]

/-- The first to `OPV`, and the second into `ymm5–ymm9`. -/
def stage2b : List Instr :=
  (List.range 5).flatMap fun j => [st (OPV + 32 * j) (5 + j), mov (5 + j) j]

/-- Stage 2's operands, both carried. -/
def stage2 : List Instr := stage2a ++ carry (5 + ·) ++ carry id ++ stage2b

/-- From `(x₃', t, x₂', a24 E)` in `ymm0–ymm4` and stage 2's first operand
at `OPV`: `(1, AA + a24 E, 1, x₁)` into `ymm5–ymm9` and `(x₂', E, x₃', t)` into
`ymm0–ymm4`, neither carried. -/
def stage3a : List Instr :=
  (List.range 5).flatMap fun j =>
    [ld 10 (OPV + 32 * j), perm 11 10 (ord 2 2 2 2), perm 12 j (ord 3 3 3 3), v .vpaddq 11 11 12,
      ld 12 (KX1 + 32 * j), blend (5 + j) 12 11 (lanes false true false false),
      perm 11 j (ord 2 0 0 1), perm 12 10 (ord 3 3 3 3), blend j 11 12 (lanes false true false false)]

/-- The second to `OPG`. -/
def stage3b : List Instr := (List.range 5).flatMap fun j => [st (OPG + 32 * j) j]

/-- Stage 3's operands, both carried. -/
def stage3 : List Instr := stage3a ++ carry (5 + ·) ++ carry id ++ stage3b

/-- One iteration, for the bit `t = rbx - 1`: `swap ^= k_t` into the mask
`ymm15 = -swap` (as `step`), the swap, then the three stages. -/
def vstep : List Instr :=
  [.alu .sub .rbx (.imm 1), .movzx8 .rax { base := .rdi, index := some .rbx, disp := BITS },
    .mov .rdx (.mem (sc SWAP)), .alu .xor .rdx (.reg .rax), .store (sc SWAP) .rax,
    .mov32 .rcx (.imm 0), .alu .sub .rcx (.reg .rdx),
    .vop (.vmovq (y 15) .rcx), .vop (.vpbroadcastq .l256 (y 15) (y 15))] ++
  vswap ++ stage1 ++ mul4 OPL ++ stage2 ++ mul4 OPV ++ stage3 ++ mul4 OPG ++
  [.alu .test .rbx (.reg .rbx)]

/-! ## Before and after the loop -/

/-- `r` into each quadword of `ymm d`. -/
def bcast (d : Nat) (r : Reg) : List Instr :=
  [.vop (.vmovq (y d) r), .vop (.vpbroadcastq .l256 (y d) (y d))]

/-- The constants into general-purpose registers: `2⁵¹ - 1`, 19, the bias's
limbs, `2¹³ - 1`, `2²⁶ - 1`, `2³⁹ - 1`, 1 and `a24`. -/
def consts : List Instr :=
  [.movImm64 .rax 0x7ffffffffffff, .mov32 .rcx (.imm 19),
    .movImm64 .rdx (0x4000000000000000 - 38912), .movImm64 .rbp (0x4000000000000000 - 2048),
    .mov32 .r8 (.imm 0x1fff), .mov32 .r9 (.imm 0x3ffffff), .movImm64 .r10 0x7fffffffff,
    .mov32 .r11 (.imm 1), .mov32 .r12 (.imm 121665)]

/-- The constants into the working space, and the ladder's first state
`(1, 0, x₁, 1)` into `ymm0–ymm4`, with `ymm9 = 2⁵¹ - 1`, `ymm13 = (1, 0, 0,
1)`, `ymm14 = (1, 0, 1, 0)`, `ymm15 = (0, 0, 0, a24)` and `ymm12 = 0`: the
limbs of `x₁`, from its words `w₀–w₃` at `X1` (`x₁₀ = w₀ mod 2⁵¹`,
`x₁₁ = w₀ >> 51 | (w₁ mod 2³⁸) << 13`, …, `x₁₄ = w₃ >> 12`), each in every
quadword of `ymm0–ymm4`, then blended with the constants. -/
def vinit : List Instr :=
  bcast 9 .rax ++ [st KM 9] ++ bcast 10 .rcx ++ [st K19 10] ++ bcast 10 .rdx ++ [st KB0 10] ++
  bcast 10 .rbp ++ [st KB1 10] ++ bcast 10 .r8 ++ [st K13 10] ++ bcast 10 .r9 ++ [st K26 10] ++
  bcast 10 .r10 ++ [st K39 10] ++
  [.vop (.vmovq (y 10) .r11), perm 13 10 (ord 0 1 1 0), perm 14 10 (ord 0 1 0 1),
    .vop (.vmovq (y 10) .r12), perm 15 10 (ord 1 1 1 0), zero 12,
    ld 10 X1, perm 5 10 (ord 0 0 0 0), perm 6 10 (ord 1 1 1 1), perm 7 10 (ord 2 2 2 2),
    perm 8 10 (ord 3 3 3 3),
    v .vpand 0 5 9,
    srl 1 5 51, srl 11 9 13, v .vpand 11 6 11, sll 11 11 13, v .vpor 1 1 11,
    srl 2 6 38, srl 11 9 26, v .vpand 11 7 11, sll 11 11 26, v .vpor 2 2 11,
    srl 3 7 25, srl 11 9 39, v .vpand 11 8 11, sll 11 11 39, v .vpor 3 3 11,
    srl 4 8 12] ++
  ((List.range 5).flatMap fun j =>
    [blend 11 (if j = 0 then 14 else 12) j (lanes false false false true), st (KX1 + 32 * j) 11,
      st (KA24 + 32 * j) (if j = 0 then 15 else 12),
      blend j (if j = 0 then 13 else 12) j (lanes false false true false)])

/-- The constants, and the ladder's first state. -/
def vsetup : List Instr := consts ++ vinit

/-- `vfinish` after the carries. -/
def vpack : List Instr :=
  [ld 10 KM] ++
  ([0, 1, 2, 3].flatMap fun k =>
    [srl 11 k 51, v .vpand k k 10, v .vpaddq (k + 1) (k + 1) 11]) ++
  [ld 11 K13, v .vpand 12 1 11, sll 12 12 51, v .vpor 5 0 12,
    srl 6 1 13, ld 11 K26, v .vpand 12 2 11, sll 12 12 38, v .vpor 6 6 12,
    srl 7 2 26, ld 11 K39, v .vpand 12 3 11, sll 12 12 25, v .vpor 7 7 12,
    srl 8 3 39, sll 12 4 12, v .vpor 8 8 12,
    v .vpunpcklqdq 0 5 6, v .vpunpckhqdq 1 5 6, v .vpunpcklqdq 2 7 8, v .vpunpckhqdq 3 7 8,
    .vop (.vperm2i128 (y 5) (y 0) (y 2) 0x20), .vop (.vperm2i128 (y 6) (y 1) (y 3) 0x20),
    .vop (.vperm2i128 (y 7) (y 0) (y 2) 0x31), .vop (.vperm2i128 (y 8) (y 1) (y 3) 0x31),
    st X2 5, st Z2 6, st X3 7, st Z3 8, .vop .vzeroupper]

/-- After the loop: the lanes of `ymm0–ymm4` carried, twice, and then from
the lowest limb up (so that each limb but the top one is below `2⁵¹`); then
put into four 64-bit words (`w₀ = x₀ | (x₁ mod 2¹³) << 51`,
`w₁ = x₁ >> 13 | (x₂ mod 2²⁶) << 38`, `w₂ = x₂ >> 26 | (x₃ mod 2³⁹) << 25`,
`w₃ = x₃ >> 39 | x₄ << 12`), one lane of words per register, transposed
into one field element per register and stored to the slots `x2, z2, x3,
z3` (consecutive). -/
def vfinish : List Instr := carry id ++ carry id ++ vpack

/-- `c` with MXCSR `0x1FBF`, through `[rdi + MX]`: MXCSR saved in `r11`,
and loaded back after `c`, which must not write `r11` (as ML-KEM's
`withMxcsr`). -/
def withMxcsr (c : Prog isa) : Prog isa :=
  .seq (.block [.stmxcsr (sc MX), .mov32 .r11 (.mem (sc MX)), .alu32 .and .r11 (.imm 0xFFFF)])
    (.seq (.seq (.block [.mov32 .rax (.imm 0x1FBF), .store32 (sc (MX + 4)) .rax,
        .ldmxcsr (sc (MX + 4)), .lfence]) (.seq c (.block [.lfence])))
      (.block [.store32 (sc MX) .r11, .ldmxcsr (sc MX)]))

/-- The ladder: `vsetup`, then with MXCSR `0x1FBF` the 255 iterations and
`vfinish`. -/
def vladder : Prog isa :=
  .seq (.block vsetup) (withMxcsr (.seq (.block [.mov32 .rbx (.imm 255)])
    (.seq (.loop (.block vstep) .ne) (.block vfinish))))

end Ifma

/-- X25519 with the ladder `Ifma.vladder`, and `adx`'s field multiplications
for the inversion. -/
def x25519Ifma : Prog isa := x25519Of adx Ifma.vladder

end VG.Impl.X25519.X86_64
