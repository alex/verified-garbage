import VerifiedGarbage.TCB.AArch64.Isa

/-!
# X25519: AArch64 implementation

`vg_x25519(out = x0, scalar = x1, point = x2, scratch = x3)`.

This backend predates the carry-flag and multiply-high ISA extensions. A field
element is fifteen 17-bit limbs, `x = Σ xᵢ 2^(17 i)` (`255 = 15 · 17`, so
`2²⁵⁵ ≡ 19` modulo `p = 2²⁵⁵ - 19` folds a product's upper half onto its
lower half), each a 64-bit word: the products of two limbs, and their sums,
fit in 64 bits with room to spare, so limbs need not be fully carried
between operations. An element is any such number, standing for its residue
modulo `p`; only the result is reduced fully.

Every element lives in the working space (`x3`), in a slot of 128 bytes at
a constant offset (`slot n`, `X1`, …):

* `[0, 48)`: our caller's `x19`–`x24`, restored on return;
* the slots from `64` on: `x1, x2, z2, x3, z3`, the ladder's temporaries
  `A, …, CB`, and the inversion's `T`;
* `BITS` (256 bytes): byte `t` is bit `t` of the clamped scalar.

Registers: `x0` is `out` and `x3` the working space throughout; `x23` is the
counter of the loops and `x24` the ladder's `swap`. The field operations use
`x1, x2, x4`–`x16` (the limbs, `dreg`), `x17` and `x19` (loaded words), and
`x20`–`x22` (a sum and constants).

The arithmetic, on limbs below `2²⁶` (products below `2⁵²`):

* `mul`: column `k` of the product (`col`) is `Σ_{i ≤ k} aᵢ b_{k-i} + 19 ·
  Σ_{i > k} aᵢ b_{k+15-i}`, each column into its own register; then the
  carries (`carry`) from limb 0 to 14, the carry out of limb 14 folded into
  limb 0 as 19 times it, and two more carries, which leaves limbs below
  `2¹⁹`;
* `mulSmall` by `a24 = 121665`, each limb multiplied and then carried;
* `add` limb by limb; `sub` adds `16 p` (limbs `2²¹ - 304`, `2²¹ - 16`, …)
  before subtracting, so that no limb is negative;
* `cswap` with the mask `0 - swap`, as RFC 7748 §5 describes;
* `freeze`: the full reduction of the result: two rounds of carries leave
  `x < 2²⁵⁵` with 17-bit limbs, the carry out of `x + 19` is `q = 1` iff
  `x ≥ p`, and `x + 19 q` with bit 255 dropped is `x - q p`; the limbs are
  then packed into four 64-bit words.

The ladder follows RFC 7748 §5 operation by operation, over the bits of the
scalar from 254 down to 0 (the counter `x23`, with the bit's address
`x3 + x23 + BITS`). The inversion `z2^(p-2)` uses the ref10 addition chain: 254 squarings
and 11 multiplications, with public counters for runs of squarings.

The only branches are on the loop counters, and every address is a pointer
plus a constant or a counter, so only the pointers can affect timing.
-/

namespace VG.Impl.X25519.AArch64

open VG.AArch64

/-! ## Registers and the layout of the working space -/

/-- The registers of the limbs `0, …, 14`. -/
def DR : List Reg := [.x1, .x2, .x4, .x5, .x6, .x7, .x8, .x9, .x10, .x11, .x12, .x13, .x14, .x15,
  .x16]

/-- The register of limb `k`. -/
def dreg (k : Nat) : Reg := DR.getD k .x16

/-- Where our caller's `x19`–`x24` are saved. -/
def SAVE : Nat := 0

/-- The offset of slot `n`. -/
def slot (n : Nat) : Nat := 64 + 128 * n

def X1 : Nat := slot 0
def X2 : Nat := slot 1
def Z2 : Nat := slot 2
def X3 : Nat := slot 3
def Z3 : Nat := slot 4
def A : Nat := slot 5
def B : Nat := slot 6
def C : Nat := slot 7
def D : Nat := slot 8
def AA : Nat := slot 9
def BB : Nat := slot 10
def E : Nat := slot 11
def DA : Nat := slot 12
def CB : Nat := slot 13
def T : Nat := slot 14
/-- The number of slots. -/
def NSLOT : Nat := 15

/-- The bits of the scalar. -/
def BITS : Nat := slot NSLOT

/-- `[x3 + off]` into `t`. -/
def ld (t : Reg) (off : Nat) : Instr := .ldr .x t .x3 off

/-- `t` into `[x3 + off]`. -/
def st (t : Reg) (off : Nat) : Instr := .str .x t .x3 off

/-! ## Field arithmetic -/

/-- `d += [x3 + oa] · [x3 + ob]`. -/
def mac (d : Reg) (oa ob : Nat) : List Instr := [ld .x17 oa, ld .x19 ob, .madd .x d .x17 .x19 d]

/-- A chain of `mac`s. -/
def macs (d : Reg) (L : List (Nat × Nat)) : List Instr := L.flatMap fun p => mac d p.1 p.2

/-- The products `aᵢ b_{k-i}` of column `k`, as offsets. -/
def loPairs (a b k : Nat) : List (Nat × Nat) :=
  (List.range (k + 1)).map fun i => (a + 8 * i, b + 8 * (k - i))

/-- The products `aᵢ b_{k+15-i}` (`i = k + 1 + j`) that fold into column `k`. -/
def hiPairs (a b k : Nat) : List (Nat × Nat) :=
  (List.range (14 - k)).map fun j => (a + 8 * (k + 1 + j), b + 8 * (14 - j))

/-- Column `k` of the product of `[a]` and `[b]`, into `dreg k` (with 19 in
`x21`). -/
def col (a b k : Nat) : List Instr :=
  [.movz .x (dreg k) 0 0] ++ macs (dreg k) (loPairs a b k) ++ [.movz .x .x20 0 0] ++
    macs .x20 (hiPairs a b k) ++ [.madd .x (dreg k) .x20 .x21 (dreg k)]

/-- The carry out of limb `k` into limb `k'` (with `2¹⁷ - 1` in `x22`). -/
def carryStep (k k' : Nat) : List Instr :=
  [.lsr .x .x17 (dreg k) 17, .logic .and .x (dreg k) (dreg k) .x22, .add .x (dreg k') (dreg k') .x17]

/-- The carry out of limb 14, times 19, into limb 0 (with 19 in `x21`). -/
def foldTop : List Instr :=
  [.lsr .x .x17 (dreg 14) 17, .logic .and .x (dreg 14) (dreg 14) .x22,
    .madd .x (dreg 0) .x17 .x21 (dreg 0)]

/-- `2¹⁷ - 1` into `x22`. -/
def mask17 : List Instr := [.movz .x .x22 0xffff 0, .movk .x .x22 1 1]

/-- 19 into `x21`. -/
def const19 : List Instr := [.movz .x .x21 19 0]

/-- The carries from limb 0 to 14. -/
def chain : List Instr := (List.range 14).flatMap fun k => carryStep k (k + 1)

/-- The carries of a product's columns (with 19 in `x21`). -/
def carry : List Instr := mask17 ++ chain ++ foldTop ++ carryStep 0 1 ++ carryStep 1 2

/-- The limbs into `[x3 + o]`. -/
def store (o : Nat) : List Instr := (List.range 15).map fun k => st (dreg k) (o + 8 * k)

/-- `[o] = [a] · [b]` (`o` may be `a` or `b`: every load precedes the stores). -/
def mul (o a b : Nat) : List Instr :=
  const19 ++ (List.range 15).flatMap (col a b) ++ carry ++ store o

/-- `a24 = 121665` into `x20`. -/
def constA24 : List Instr := [.movz .x .x20 0xdb41 0, .movk .x .x20 1 1]

/-- The limbs of `[a]` times `a24`. -/
def scale (a : Nat) : List Instr :=
  (List.range 15).flatMap fun k => [ld .x17 (a + 8 * k), .mul .x (dreg k) .x17 .x20]

/-- `[o] = a24 · [a]`. -/
def mulSmall (o a : Nat) : List Instr := const19 ++ constA24 ++ scale a ++ carry ++ store o

/-- `[o] = [a] + [b]`, limb by limb. -/
def add (o a b : Nat) : List Instr :=
  (List.range 15).flatMap fun i =>
    [ld .x17 (a + 8 * i), ld .x19 (b + 8 * i), .add .x .x17 .x17 .x19, st .x17 (o + 8 * i)]

/-- The limbs of `16 p` into `x20` (limb 0: `2²¹ - 304`) and `x21` (the others: `2²¹ - 16`). -/
def const16p : List Instr :=
  [.movz .x .x20 0xfed0 0, .movk .x .x20 0x1f 1, .movz .x .x21 0xfff0 0, .movk .x .x21 0x1f 1]

/-- The register holding limb `i` of `16 p`. -/
def preg (i : Nat) : Reg := if i = 0 then .x20 else .x21

/-- `[o] = [a] + 16 p - [b]`, limb by limb. -/
def sub (o a b : Nat) : List Instr :=
  const16p ++ (List.range 15).flatMap fun i =>
    [ld .x17 (a + 8 * i), ld .x19 (b + 8 * i), .add .x .x17 .x17 (preg i), .sub .x .x17 .x17 .x19,
      st .x17 (o + 8 * i)]

/-- Swaps `[x]` and `[y]` if the mask `x22` is all ones (and not if it is
zero): `d = x22 ∧ (x ⊕ y)`, `x ⊕= d`, `y ⊕= d`, limb by limb. -/
def cswap (x y : Nat) : List Instr :=
  (List.range 15).flatMap fun i =>
    [ld .x17 (x + 8 * i), ld .x19 (y + 8 * i), .logic .eor .x .x20 .x17 .x19,
      .logic .and .x .x20 .x20 .x22, .logic .eor .x .x17 .x17 .x20, .logic .eor .x .x19 .x19 .x20,
      st .x17 (x + 8 * i), st .x19 (y + 8 * i)]

/-- `[o] = [a]`. -/
def copy (o a : Nat) : List Instr :=
  (List.range 15).flatMap fun i => [ld .x17 (a + 8 * i), st .x17 (o + 8 * i)]

/-! ## The ladder -/

/-- The mask `0 - swap` into `x22`, for `swap` in `x20`. -/
def maskOf : List Instr := [.movz .x .x22 0 0, .sub .x .x22 .x22 .x20]

/-- One iteration of the ladder, for the bit `t = x23 - 1`: `k_t` from
`BITS`, `swap ^ k_t` into `x20`, `swap = k_t`, the swaps, and the formulas
of RFC 7748 §5 in order. -/
def step : List Instr :=
  [.subImm .x .x23 .x23 1, .add .x .x17 .x3 .x23, .ldrb .x19 .x17 BITS,
    .logic .eor .x .x20 .x24 .x19, .addImm .x .x24 .x19 0] ++ maskOf ++
  cswap X2 X3 ++ cswap Z2 Z3 ++
  add A X2 Z2 ++ mul AA A A ++ sub B X2 Z2 ++ mul BB B B ++ sub E AA BB ++
  add C X3 Z3 ++ sub D X3 Z3 ++ mul DA D A ++ mul CB C B ++
  add X3 DA CB ++ mul X3 X3 X3 ++ sub Z3 DA CB ++ mul Z3 Z3 Z3 ++ mul Z3 X1 Z3 ++
  mul X2 AA BB ++ mulSmall Z2 E ++ add Z2 AA Z2 ++ mul Z2 E Z2

/-- The 255 iterations, for `t` from 254 down to 0, with `swap = 0` first. -/
def ladder : Prog isa :=
  .seq (.block [.movz .x .x23 255 0, .movz .x .x24 0 0]) (.loop (.block step) (.nonzero .x .x23))

/-- The swap after the loop. -/
def lastSwap : List Instr := [.addImm .x .x20 .x24 0] ++ maskOf ++ cswap X2 X3 ++ cswap Z2 Z3

/-! ## Inversion: ref10's 254-square, 11-multiply addition chain.
The ladder's dead temporaries A, B and C are reused, with T holding the result. -/

def sqn (o a n : Nat) : Prog isa :=
  .seq (.block (copy o a ++ [.movz .x .x23 n 0]))
    (.loop (.block (mul o o o ++ [.subImm .x .x23 .x23 1])) (.nonzero .x .x23))

def invChain : Prog isa :=
  .seq (.block (mul A Z2 Z2)) <|
  .seq (sqn T A 2) <|
  .seq (.block (mul T Z2 T ++ mul A A T ++ mul B A A ++ mul T T B)) <|
  .seq (sqn B T 5) <| .seq (.block (mul T B T)) <|
  .seq (sqn B T 10) <| .seq (.block (mul B B T)) <|
  .seq (sqn C B 20) <| .seq (.block (mul B C B)) <|
  .seq (sqn B B 10) <| .seq (.block (mul T B T)) <|
  .seq (sqn B T 50) <| .seq (.block (mul B B T)) <|
  .seq (sqn C B 100) <| .seq (.block (mul B C B)) <|
  .seq (sqn B B 50) <| .seq (.block (mul T B T)) <|
  .seq (sqn T T 5) (.block (mul T T A))

def invert : Prog isa :=
  .seq (.block (copy A Z2 ++ copy B Z2 ++ copy C Z2 ++ copy T Z2)) invChain

/-! ## Decoding -/

/-- The words of the u-coordinate (`[x2]`) into `x4`–`x7`. -/
def loadU : List Instr := [.ldr .x .x4 .x2 0, .ldr .x .x5 .x2 8, .ldr .x .x6 .x2 16, .ldr .x .x7 .x2 24]

/-- The register holding word `q` of the u-coordinate. -/
def ureg (q : Nat) : Reg := [Reg.x4, .x5, .x6, .x7].getD q .x7

/-- Limb `i` (bits `17 i` to `17 i + 16`) of the u-coordinate into `x17`: from
word `q = 17 i / 64`, and from the next one if it straddles them. -/
def limbOf (i : Nat) : List Instr :=
  let q := 17 * i / 64
  let r := 17 * i % 64
  if r + 17 ≤ 64 then [.lsr .x .x17 (ureg q) r, .logic .and .x .x17 .x17 .x22]
  else [.lsr .x .x17 (ureg q) r, .lsl .x .x19 (ureg (q + 1)) (64 - r), .add .x .x17 .x17 .x19,
    .logic .and .x .x17 .x17 .x22]

/-- `x1 = x3 = u` (the top bit masked: limb 14 is bits 238 to 254). -/
def decode : List Instr :=
  loadU ++ mask17 ++ (List.range 15).flatMap fun i =>
    limbOf i ++ [st .x17 (X1 + 8 * i), st .x17 (X3 + 8 * i)]

/-- `BITS[8i + j] = bit j of scalar byte i` (with 1 in `x20`). -/
def bitsOf (i : Nat) : List Instr :=
  .ldrb .x17 .x1 i :: (List.range 8).flatMap fun j =>
    [.lsr .x .x19 .x17 j, .logic .and .x .x19 .x19 .x20, .strb .x19 .x3 (BITS + 8 * i + j)]

/-- The bits of the scalar, clamped: bits 0, 1, 2 cleared and bit 254 set. -/
def bits : List Instr :=
  [.movz .x .x20 1 0] ++ (List.range 32).flatMap bitsOf ++
  [.movz .x .x19 0 0, .strb .x19 .x3 BITS, .strb .x19 .x3 (BITS + 1), .strb .x19 .x3 (BITS + 2),
    .strb .x20 .x3 (BITS + 254)]

/-- The callee-saved registers we use, saved at `SAVE`. -/
def saved : List Reg := [.x19, .x20, .x21, .x22, .x23, .x24]

def save : List Instr := (List.range 6).map fun k => st (saved.getD k .x19) (SAVE + 8 * k)

def restore : List Instr := (List.range 6).map fun k => ld (saved.getD k .x19) (SAVE + 8 * k)

/-- `[o] = 0` (with 0 in `x17`). -/
def zero (o : Nat) : List Instr := (List.range 15).map fun i => st .x17 (o + 8 * i)

/-- `z2 = 0`, `x2 = 1`, `z3 = 1`. -/
def initSlots : List Instr :=
  [.movz .x .x17 0 0] ++ zero Z2 ++ (zero X2 ++ [.movz .x .x19 1 0, st .x19 X2]) ++ copy Z3 X2

def setup : List Instr := save ++ decode ++ bits ++ initSlots

/-! ## Encoding -/

/-- The limbs of `[a]` into the limb registers. -/
def load (a : Nat) : List Instr := (List.range 15).map fun k => ld (dreg k) (a + 8 * k)

/-- The carry out of `x + 19` (limbs `x`), which is 1 iff `x ≥ p` for
`x < 2²⁵⁵`, into `x17`. -/
def quot : List Instr :=
  [.addImm .x .x17 (dreg 0) 19, .lsr .x .x17 .x17 17] ++
    (List.range 14).flatMap fun k => [.add .x .x17 (dreg (k + 1)) .x17, .lsr .x .x17 .x17 17]

/-- The fully reduced `x` from limbs below `2¹⁹`: two rounds of carries (so
`x < 2²⁵⁵`), then `x + 19 q` modulo `2²⁵⁵`. -/
def freeze : List Instr :=
  mask17 ++ const19 ++ chain ++ foldTop ++ chain ++ foldTop ++ quot ++
    [.madd .x (dreg 0) .x17 .x21 (dreg 0)] ++ chain ++ [.logic .and .x (dreg 14) (dreg 14) .x22]

/-- Limb `i` shifted to its place in word `j`, into `t`. -/
def place (t : Reg) (i j : Nat) : Instr :=
  if 64 * j ≤ 17 * i then .lsl .x t (dreg i) (17 * i - 64 * j) else .lsr .x t (dreg i) (64 * j - 17 * i)

/-- The limbs that have bits in word `j`. -/
def wordLimbs (j : Nat) : List Nat :=
  (List.range 15).filter fun i => 64 * j < 17 * i + 17 ∧ 17 * i < 64 * j + 64

/-- Word `j` of the fully reduced limbs, into `[x0 + 8 j]`. -/
def packWord (j : Nat) : List Instr :=
  match wordLimbs j with
  | [] => []
  | i :: is => place .x17 i j :: is.flatMap (fun i => [place .x19 i j, .add .x .x17 .x17 .x19]) ++
      [.str .x .x17 .x0 (8 * j)]

def pack : List Instr := (List.range 4).flatMap packWord

/-- `x2 · z2^(p-2)`, reduced fully, to `out`, and the saved registers restored. -/
def finish : List Instr := mul X2 X2 T ++ load X2 ++ freeze ++ pack ++ restore

def x25519 : Prog isa :=
  .seq (.block setup) <| .seq ladder <| .seq (.block lastSwap) <| .seq invert (.block finish)

end VG.Impl.X25519.AArch64
