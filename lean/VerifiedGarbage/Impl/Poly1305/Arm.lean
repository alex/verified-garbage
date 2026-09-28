import VerifiedGarbage.TCB.Arm.Isa

/-!
# Poly1305: 32-bit ARM implementation

The only multiplication is `mul` (the low 32 bits of a 32 × 32-bit product),
so the arithmetic is in radix `2¹³`: a number below `2¹³⁰` is ten 13-bit
limbs `x0 + 2¹³ x1 + … + 2¹¹⁷ x9`, a product of two limbs fits in 26 bits,
and a sum of ten products (with the factor 5 of the reduction below) fits in
32 bits. The product `h r` of two such numbers, reduced modulo `p = 2¹³⁰ - 5`
using `2¹³⁰ ≡ 5`, is ten columns

  `dk = Σ_{j ≤ k} hj r(k-j) + Σ_{j > k} 5 hj r(k+10-j)`.

Between blocks the columns are kept as they come out of the multiplication
(`dk < 2³²`, not reduced to 13 bits): the next block's limbs are added to
them, and then they are carried (each limb's bits from 13 up added to the
next, the top one's times 5 to the bottom) into `h` with limbs below
`2¹³ + 2⁹`, which keeps the next columns below `2³²`.

The state (`state`, 128 bytes, see `VG.Spec.Poly1305.Repr`):

* `[0, 24)`: the accumulator in six little-endian words (the last one
  zero), fully reduced, between calls. During a call: the carried `h`, two
  limbs per word (`h(2i) + 2¹⁶ h(2i+1)` at `4i`), while it is multiplied;
  the top column `d9` at `16` between blocks; the number of blocks left (in
  `blocks`) or the pointer `out` (in `finalize`) at `20`;
* `[24, 56)`: the key: `r` (`[24, 40)`) and `s` (`[40, 56)`);
* `[56, 88)`: the saved `r4`–`r11`;
* `[88, 120)`: the limbs `r0`–`r3`, `r5`–`r8` of the clamped `r`, and
  `[120, 122)`: `r4` and `r9`, one byte each (they are below `2⁸`);
* `[124, 128)`: the pointer to the next block (in `blocks`) or the tail's
  length (in `finalize`).

Registers: `r0` = `state`. The columns `d0`–`d8` are in `r3`–`r11` (`yr`),
`d9` in memory, then in `r1`, while a block is added and carried; while `h`
is multiplied by `r`, row by row, the columns are in `r3`–`r12` (`xr`),
`hj` (then `5 hj`) in `r1` and `ri` in `r2`.

The only branches are on the block count and the tail's length, and every
address is `state`, a pointer or a pointer plus a constant or a count, so
only the pointers and lengths can affect timing.
-/

namespace VG.Impl.Poly1305.Arm

open VG.Arm

/-! ## Registers and offsets -/

/-- The register of column `k` while a block is added and carried. -/
def yr : Nat → Reg
  | 0 => .r3 | 1 => .r4 | 2 => .r5 | 3 => .r6 | 4 => .r7 | 5 => .r8 | 6 => .r9 | 7 => .r10
  | 8 => .r11 | _ => .r1

/-- The register of column `k` while `h` is multiplied by `r`. -/
def xr : Nat → Reg
  | 0 => .r3 | 1 => .r4 | 2 => .r5 | 3 => .r6 | 4 => .r7 | 5 => .r8 | 6 => .r9 | 7 => .r10
  | 8 => .r11 | _ => .r12

/-- Where limb `i` of the clamped `r` is: a word, or a byte for `r4` and `r9`. -/
def rOff : Nat → Nat
  | 0 => 88 | 1 => 92 | 2 => 96 | 3 => 100 | 4 => 120
  | 5 => 104 | 6 => 108 | 7 => 112 | 8 => 116 | _ => 121

/-- The top column between blocks. -/
def d9Off : Nat := 16
/-- The number of blocks left (`blocks`), or `out` (`finalize`). -/
def cntOff : Nat := 20
/-- The next block (`blocks`), or the tail's length (`finalize`). -/
def ptrOff : Nat := 124

/-- The callee-saved registers we use, saved at `56 + 4i`. -/
def savedReg : Nat → Reg
  | 0 => .r4 | 1 => .r5 | 2 => .r6 | 3 => .r7 | 4 => .r8 | 5 => .r9 | 6 => .r10 | _ => .r11

def saveRegs : List Instr := (List.range 8).flatMap fun i => [.str (savedReg i) .r0 (56 + 4 * i)]
def restoreRegs : List Instr := (List.range 8).flatMap fun i => [.ldr (savedReg i) .r0 (56 + 4 * i)]

/-! ## Adding a 128-bit number to the columns

The 16 bytes at `r1`, four little-endian words, are added limb by limb: limb
`k` is bits `13k` to `13k + 12`. A piece `(k, a, b)` of a word `w` adds
`(w << a) >> b` (or `w >> b` if `a = 0`) to column `k`, using `r12`. -/

/-- The pieces of word `i` (limb 9, the top 11 bits of word 3, is added
separately). -/
def pieces : Nat → List (Nat × Nat × Nat)
  | 0 => [(0, 19, 19), (1, 6, 19), (2, 0, 26)]
  | 1 => [(2, 25, 19), (3, 12, 19), (4, 0, 20)]
  | 2 => [(4, 31, 19), (5, 18, 19), (6, 5, 19), (7, 0, 27)]
  | _ => [(7, 24, 19), (8, 11, 19)]

def piece : Nat × Nat × Nat → List Instr
  | (k, 0, b) => [.dp .add (yr k) (yr k) (.shifted .r2 .lsr b)]
  | (k, a, b) => [.mov .r12 (.shifted .r2 .lsl a), .dp .add (yr k) (yr k) (.shifted .r12 .lsr b)]

/-- Word `i` into `r2`, and its pieces added. -/
def addWord (i : Nat) : List Instr := .ldr .r2 .r1 (4 * i) :: (pieces i).flatMap piece

/-- Limbs 0–8 added to `r3`–`r11`; word 3 is left in `r2`. -/
def addWords : List Instr := (List.range 4).flatMap addWord

/-- Column 9 from memory, plus limb 9 (and `2¹²⁸` if `pad`), into `r1`. -/
def addTop (pad : Bool) : List Instr :=
  [.ldr .r1 .r0 d9Off, .dp .add .r1 .r1 (.shifted .r2 .lsr 21)] ++
  if pad then [.dp .add .r1 .r1 (.imm 2048)] else []

/-- Zero `r3`–`r11`. -/
def zeroY : List Instr := (List.range 9).flatMap fun k => [.mov (yr k) (.imm 0)]

/-! ## Carrying -/

/-- The mask of a limb, in `r2`. -/
def mask : Instr := .movw .r2 0x1fff

/-- Column `k`'s bits from 13 up added to column `k + 1`. -/
def carryStep (k : Nat) : List Instr :=
  [.dp .add (yr (k + 1)) (yr (k + 1)) (.shifted (yr k) .lsr 13), .dp .and (yr k) (yr k) (.reg .r2)]

/-- Carry every column; column 9's bits from 13 up are added, times 5, to
column 0, and then column 0 is carried once more. -/
def carryFold : List Instr :=
  mask :: (List.range 9).flatMap carryStep ++
  [.mov .r12 (.shifted .r1 .lsr 13), .dp .and .r1 .r1 (.reg .r2),
   .dp .add .r12 .r12 (.shifted .r12 .lsl 2), .dp .add .r3 .r3 (.reg .r12)] ++ carryStep 0

/-! ## Absorbing a block -/

/-- `h`, two limbs per word, at `[0, 20)`. -/
def pack : List Instr :=
  (List.range 5).flatMap fun i =>
    [.dp .add (yr (2 * i)) (yr (2 * i)) (.shifted (yr (2 * i + 1)) .lsl 16), .str (yr (2 * i)) .r0 (4 * i)]

/-- Zero the columns. -/
def zeroX : List Instr := (List.range 10).flatMap fun k => [.mov (xr k) (.imm 0)]

/-- `hj` into `r1`. -/
def loadH (j : Nat) : List Instr :=
  if j % 2 = 0 then [.ldr .r1 .r0 (2 * j), .mov .r1 (.shifted .r1 .lsl 16), .mov .r1 (.shifted .r1 .lsr 16)]
  else [.ldr .r1 .r0 (2 * (j - 1)), .mov .r1 (.shifted .r1 .lsr 16)]

/-- `ri` into `r2`. -/
def loadR (i : Nat) : Instr := if i = 4 ∨ i = 9 then .ldrb .r2 .r0 (rOff i) else .ldr .r2 .r0 (rOff i)

/-- `hj ri` (or `5 hj ri`, once `i + j ≥ 10`) added to column `i + j mod 10`. -/
def mac (j i : Nat) : List Instr :=
  (if 0 < j ∧ i + j = 10 then [.dp .add .r1 .r1 (.shifted .r1 .lsl 2)] else []) ++
  [loadR i, .mul .r2 .r1 .r2, .dp .add (xr ((i + j) % 10)) (xr ((i + j) % 10)) (.reg .r2)]

def row (j : Nat) : List Instr := loadH j ++ (List.range 10).flatMap (mac j)

/-- The columns of `h r`. -/
def multiply : List Instr := zeroX ++ (List.range 10).flatMap row

/-- Absorbing the 16 bytes at `r1` (plus `2¹²⁸` if `pad`) into the columns:
`d0`–`d8` in `r3`–`r11` and `d9` in memory, before and after. -/
def absorb (pad : Bool) : List Instr :=
  addWords ++ addTop pad ++ carryFold ++ pack ++ multiply ++ [.str .r12 .r0 d9Off]

/-! ## Setup -/

/-- The clamped `r`, as four words at `[88, 104)`. -/
def clampWords : List Instr :=
  [.movw .r2 0xffff, .movt .r2 0x0fff, .ldr .r1 .r0 24, .dp .and .r1 .r1 (.reg .r2), .str .r1 .r0 88,
   .movw .r2 0xfffc, .movt .r2 0x0fff] ++
  (List.range 3).flatMap fun i =>
    [.ldr .r1 .r0 (28 + 4 * i), .dp .and .r1 .r1 (.reg .r2), .str .r1 .r0 (92 + 4 * i)]

/-- The limbs of the clamped `r`. -/
def setupR : List Instr :=
  clampWords ++ zeroY ++ [.dp .add .r1 .r0 (.imm 88)] ++ addWords ++ [.mov .r1 (.shifted .r2 .lsr 21)] ++
  [.str .r3 .r0 88, .str .r4 .r0 92, .str .r5 .r0 96, .str .r6 .r0 100, .strb .r7 .r0 120,
   .str .r8 .r0 104, .str .r9 .r0 108, .str .r10 .r0 112, .str .r11 .r0 116, .strb .r1 .r0 121]

/-- The limbs of the stored accumulator as the columns: `d0`–`d8` in
`r3`–`r11`, `d9` in memory. -/
def loadAcc : List Instr :=
  zeroY ++ [.mov .r1 (.reg .r0)] ++ addWords ++
  [.mov .r1 (.shifted .r2 .lsr 21), .ldr .r2 .r0 16, .dp .add .r1 .r1 (.shifted .r2 .lsl 11),
   .str .r1 .r0 d9Off]

/-! ## The final reduction -/

/-- Carry limbs 1–8 (after `carryFold`, only limb 1 may exceed 13 bits). -/
def carry2 : List Instr := (List.range 8).flatMap fun k => carryStep (k + 1)

/-- `c`, the bits from 130 up of `h + 5`, into `r12`. -/
def plus5 : List Instr :=
  .dp .add .r12 .r3 (.imm 5) ::
    (List.range 9).flatMap fun k => [.dp .add .r12 (yr (k + 1)) (.shifted .r12 .lsr 13)]

/-- `5 c` added to limb 0. -/
def addC : List Instr :=
  [.mov .r12 (.shifted .r12 .lsr 13), .dp .add .r12 .r12 (.shifted .r12 .lsl 2),
   .dp .add .r3 .r3 (.reg .r12)]

/-- Carry every limb, dropping bit 130. -/
def carry3 : List Instr := (List.range 9).flatMap carryStep ++ [.dp .and .r1 .r1 (.reg .r2)]

/-- The columns carried into limbs below `2¹³` (the top one at most `2¹³`),
then reduced fully: `c = ⌊(h + 5) / 2¹³⁰⌋` is 1 if `h ≥ p` (else 0), and
`h + 5 c` without its bit 130 is `h mod p`. Limbs in `r3`–`r11`, `r1`. -/
def reduceRegs : List Instr := carryFold ++ carry2 ++ plus5 ++ addC ++ carry3

def reduce : List Instr := .ldr .r1 .r0 d9Off :: reduceRegs

/-- The limbs as words: bits 0–31 in `r3`, 32–63 in `r5`, 64–95 in `r7`,
96–127 in `r10`, and 128 up in `r1`. -/
def toWords : List Instr := [
  .dp .add .r3 .r3 (.shifted .r4 .lsl 13), .dp .add .r3 .r3 (.shifted .r5 .lsl 26),
  .mov .r5 (.shifted .r5 .lsr 6), .dp .add .r5 .r5 (.shifted .r6 .lsl 7),
  .dp .add .r5 .r5 (.shifted .r7 .lsl 20),
  .mov .r7 (.shifted .r7 .lsr 12), .dp .add .r7 .r7 (.shifted .r8 .lsl 1),
  .dp .add .r7 .r7 (.shifted .r9 .lsl 14), .dp .add .r7 .r7 (.shifted .r10 .lsl 27),
  .mov .r10 (.shifted .r10 .lsr 5), .dp .add .r10 .r10 (.shifted .r11 .lsl 8),
  .dp .add .r10 .r10 (.shifted .r1 .lsl 21),
  .mov .r1 (.shifted .r1 .lsr 11)]

/-! ## `init(state = r0, key = r1)` -/

def init : Prog isa := .block (
  (List.range 8).flatMap (fun i => [.ldr .r2 .r1 (4 * i), .str .r2 .r0 (24 + 4 * i)]) ++
  .mov .r2 (.imm 0) :: (List.range 6).flatMap fun i => [.str .r2 .r0 (4 * i)])

/-! ## `blocks(state = r0, blocks = r1, n = r2)` -/

def body : Prog isa := .block (
  [.ldr .r1 .r0 ptrOff, .dp .add .r2 .r1 (.imm 16), .str .r2 .r0 ptrOff] ++ absorb true ++
  [.ldr .r1 .r0 cntOff, .subs .r1 .r1 (.imm 1), .str .r1 .r0 cntOff])

def blocks : Prog isa :=
  .seq (.block (saveRegs ++ [.str .r1 .r0 ptrOff, .str .r2 .r0 cntOff] ++ setupR ++ loadAcc ++
    [.ldr .r1 .r0 cntOff, .cmp .r1 (.imm 0)]))
  (.seq (.ite .eq (.block []) (.loop body .ne))
    (.block (reduce ++ toWords ++
      [.str .r3 .r0 0, .str .r5 .r0 4, .str .r7 .r0 8, .str .r10 .r0 12, .str .r1 .r0 16,
       .mov .r2 (.imm 0), .str .r2 .r0 20] ++ restoreRegs)))

/-! ## `finalize(state = r0, tail = r1, len = r2, out = r3)`

A non-empty tail is copied to `out`, padded with `0x01` and zeros, and
absorbed from there without `2¹²⁸`. Then `h` is reduced, `s` added, and the
sum carried and stored modulo `2¹²⁸`. -/

def copyTail : Prog isa :=
  .seq (.block [.mov .r12 (.imm 0), .str .r12 .r3 0, .str .r12 .r3 4, .str .r12 .r3 8,
      .str .r12 .r3 12, .mov .r4 (.reg .r3), .mov .r5 (.reg .r2)])
  (.seq (.loop (.block [.ldrb .r12 .r1 0, .strb .r12 .r4 0, .dp .add .r1 .r1 (.imm 1),
      .dp .add .r4 .r4 (.imm 1), .subs .r5 .r5 (.imm 1)]) .ne)
    (.block [.mov .r12 (.imm 1), .strb .r12 .r4 0]))

def finalize : Prog isa :=
  .seq (.block (saveRegs ++ [.cmp .r2 (.imm 0)]))
  (.seq (.ite .eq (.block []) copyTail)
  (.seq (.block ([.str .r3 .r0 cntOff, .str .r2 .r0 ptrOff] ++ setupR ++ loadAcc ++
      [.ldr .r1 .r0 ptrOff, .cmp .r1 (.imm 0)]))
  (.seq (.ite .eq (.block []) (.block (.ldr .r1 .r0 cntOff :: absorb false)))
    (.block (reduce ++ [.str .r1 .r0 d9Off, .dp .add .r1 .r0 (.imm 40)] ++ addWords ++ addTop false ++
      mask :: (List.range 9).flatMap carryStep ++ toWords ++
      [.ldr .r2 .r0 cntOff, .str .r3 .r2 0, .str .r5 .r2 4, .str .r7 .r2 8, .str .r10 .r2 12] ++
      restoreRegs)))))

end VG.Impl.Poly1305.Arm
