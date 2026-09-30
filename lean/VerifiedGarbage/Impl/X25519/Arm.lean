import VerifiedGarbage.TCB.Arm.Isa

/-!
# X25519: 32-bit ARM implementation

`vg_x25519(out = r0, scalar = r1, point = r2, scratch = r3)`.

The only multiplication is `mul` (the low 32 bits of a 32 × 32-bit product),
so a field element is sixteen 16-bit limbs `x0 + 2¹⁶ x1 + … + 2²⁴⁰ x15`, each
in a word of its own: a product of two limbs fits in 32 bits. Every element
is any number below `2²⁵⁶` with limbs below `2¹⁶`, standing for its residue
modulo `p = 2²⁵⁵ - 19`; only the result is reduced fully. Every element lives
in the working space, at a constant offset from its base, which is in `r0`
once the arguments are read (`out` then in `r12`):

* `[0, 32)`: the saved `r4`–`r11`;
* `x1, x2, z2, x3, z3`, the ladder's temporaries, the constant `a24`, the
  inversion's result and the final reduction's temporary, 64 bytes each
  (`X1`, …);
* the 32 limbs of a product (`ACC`, 128 bytes) and the bits of the scalar
  (`BITS`, byte `t` is bit `t` of the clamped scalar).

The arithmetic (registers `r1`–`r9`; `r6` = `0xffff`, `r8` = 38):

* `pass`: the limbs of a number from sixteen sums `c_k` (below `2³²` less a
  carry), limb `k` being `c_k` plus the carry from limb `k - 1`, modulo
  `2¹⁶`, and the carry out in `r5`;
* `tail`: the carry out (`2²⁵⁶ ≡ 38`) folded into limb 0 as `38` times itself
  and carried again (`pass` of the limbs themselves); what that carries out is
  0 or 1, and if it is 1 the limbs are small, so `38` more in limb 0 stays
  below `2¹⁶`;
* `mul`: the 32 limbs of the product row by row (Knuth's algorithm M: each
  step `a_i b_j + acc + carry` fits in 32 bits), then the limbs of
  `lo + 38 hi` (`pass`), then `tail`;
* `add`, `sub`: the limbs of `a + b` and of `a + 4p - b` (every limb of `4p`
  is at least `2¹⁶ - 1`, so no limb is negative), then `tail`;
* `cswap`: with the mask `-swap`, as RFC 7748 §5 describes;
* `freeze`: the full reduction of the result: bit 255 folded in as 19
  (`x < 2²⁵⁵ + 19`), then `x + 19 - 2²⁵⁵` selected with a mask if it is not
  negative.

The ladder follows RFC 7748 §5 operation by operation (with `a24 · E` a
multiplication by the constant element `A24`), over the bits of the scalar
from 254 down to 0 (the counter `r11`, which indexes `BITS`; `swap` in
`r10`). The inversion `z2^(p-2)` is square-and-multiply over the bits of
`p - 2 = 2²⁵⁵ - 21` from 254 down to 0 (the counter `r10`): every bit but 4
and 2 is 1.

The only branches are on the loop counters, and every address is a pointer
plus a constant or a counter, so only the pointers can affect timing.
-/

namespace VG.Impl.X25519.Arm

open VG.Arm

/-! ## The layout of the working space -/

def X1 : Nat := 64
def X2 : Nat := 128
def Z2 : Nat := 192
def X3 : Nat := 256
def Z3 : Nat := 320
def A : Nat := 384
def B : Nat := 448
def C : Nat := 512
def D : Nat := 576
def AA : Nat := 640
def BB : Nat := 704
def E : Nat := 768
def DA : Nat := 832
def CB : Nat := 896
def A24 : Nat := 960
def R : Nat := 1024
def Y : Nat := 1088
def ACC : Nat := 1152
def BITS : Nat := 1280

/-! ## Carrying -/

/-- A limb stored at `[rb, #off]`: `r3 + r5` modulo `2¹⁶` (with the mask
`r6`), and the carry `(r3 + r5) >> 16` into `r5`. -/
def carryStep (rb : Reg) (off : Nat) : List Instr :=
  [.dp .add .r3 .r3 (.reg .r5), .dp .and .r4 .r3 (.reg .r6), .str .r4 rb off,
    .mov .r5 (.shifted .r3 .lsr 16)]

/-- The limbs at `[rb, #o]` from the sums `src k` leaves in `r3` and the carry
in `r5`. -/
def pass (rb : Reg) (o : Nat) (src : Nat → List Instr) : List Instr :=
  (List.range 16).flatMap fun k => src k ++ carryStep rb (o + 4 * k)

/-- Limb `k` of `[o]`, into `r3`. -/
def ldSrc (o k : Nat) : List Instr := [.ldr .r3 .r0 (o + 4 * k)]

/-- The carry out of `[o]`, in `r5`, folded in as 38 times itself, twice. -/
def tail (o : Nat) : List Instr :=
  [.mul .r5 .r5 .r8] ++ pass .r0 o (ldSrc o) ++
    [.mul .r5 .r5 .r8, .ldr .r3 .r0 o, .dp .add .r3 .r3 (.reg .r5), .str .r3 .r0 o]

/-- The mask of a limb in `r6`, 38 in `r8` and no carry in `r5`. -/
def prologue : List Instr := [.movw .r6 0xffff, .mov .r8 (.imm 38), .mov .r5 (.imm 0)]

/-! ## Field arithmetic -/

def addSrc (a b k : Nat) : List Instr :=
  [.ldr .r3 .r0 (a + 4 * k), .ldr .r2 .r0 (b + 4 * k), .dp .add .r3 .r3 (.reg .r2)]

/-- `[o] = [a] + [b]`. -/
def add (o a b : Nat) : List Instr := prologue ++ pass .r0 o (addSrc a b) ++ tail o

/-- Limb `k` of `4p` is `subHi k - subLo k`. -/
def subHi (k : Nat) : BitVec 32 := if k = 15 then 0x20000 else 0x40000
def subLo (k : Nat) : BitVec 32 := if k = 0 then 76 else 4

def subSrc (a b k : Nat) : List Instr :=
  [.ldr .r3 .r0 (a + 4 * k), .dp .add .r3 .r3 (.imm (subHi k)), .dp .sub .r3 .r3 (.imm (subLo k)),
    .ldr .r2 .r0 (b + 4 * k), .dp .sub .r3 .r3 (.reg .r2)]

/-- `[o] = [a] - [b]`, as `[a] + 4p - [b]`. -/
def sub (o a b : Nat) : List Instr := prologue ++ pass .r0 o (subSrc a b) ++ tail o

/-- Register `r` stored into the `n` words from `o` of the working space. -/
def storeN (r : Reg) (o n : Nat) : List Instr := (List.range n).flatMap fun k => [.str r .r0 (o + 4 * k)]

/-- The words `ACC[0, 16)` zeroed. -/
def zeroAcc : List Instr := .mov .r3 (.imm 0) :: storeN .r3 ACC 16

/-- Limb `j` of row `i` (`r7` = the base plus `4 i`, `a_i` in `r1`) into
`r3`: `a_i b_j + ACC[i + j]`. -/
def rowSrc (b j : Nat) : List Instr :=
  [.ldr .r2 .r0 (b + 4 * j), .mul .r2 .r1 .r2, .ldr .r3 .r7 (ACC + 4 * j), .dp .add .r3 .r3 (.reg .r2)]

/-- Row `i` of the product: `ACC[i, i + 17) = ACC[i, i + 16) + a_i · b`. -/
def row (a b : Nat) : List Instr :=
  [.ldr .r1 .r7 a, .mov .r5 (.imm 0)] ++ pass .r7 ACC (rowSrc b) ++
    [.str .r5 .r7 (ACC + 64), .dp .add .r7 .r7 (.imm 4), .subs .r9 .r9 (.imm 1)]

/-- Limb `k` of `lo + 38 hi` for the product in `ACC`, into `r3`. -/
def mulSrc (k : Nat) : List Instr :=
  [.ldr .r3 .r0 (ACC + 4 * k), .ldr .r2 .r0 (ACC + 64 + 4 * k), .mul .r2 .r2 .r8,
    .dp .add .r3 .r3 (.reg .r2)]

/-- `[o] = [a] · [b]` (`o` may be `a` or `b`). -/
def mul (o a b : Nat) : Prog isa :=
  .seq (.block (prologue ++ zeroAcc ++ [.mov .r7 (.reg .r0), .mov .r9 (.imm 16)]))
    (.seq (.loop (.block (row a b)) .ne) (.block (.mov .r5 (.imm 0) :: pass .r0 o mulSrc ++ tail o)))

/-- Swaps limb `k` of `[x]` and `[y]` if the mask `r9` is all ones (and not
if it is zero): `d = r9 ∧ (x ⊕ y)`, `x ⊕= d`, `y ⊕= d`. -/
def cswapStep (x y k : Nat) : List Instr :=
  [.ldr .r2 .r0 (x + 4 * k), .ldr .r3 .r0 (y + 4 * k), .dp .eor .r4 .r2 (.reg .r3),
    .dp .and .r4 .r4 (.reg .r9), .dp .eor .r2 .r2 (.reg .r4), .dp .eor .r3 .r3 (.reg .r4),
    .str .r2 .r0 (x + 4 * k), .str .r3 .r0 (y + 4 * k)]

def cswap (x y : Nat) : List Instr := (List.range 16).flatMap (cswapStep x y)

/-! ## The ladder -/

/-- The mask `-swap` into `r9`. -/
def mask : List Instr := [.mov .r9 (.imm 0), .dp .sub .r9 .r9 (.reg .r10)]

/-- The start of an iteration of the ladder, for the bit `t = r11 - 1`: `k_t`
from `BITS`, `swap ^= k_t`, the swaps by the mask `-swap`, and `swap = k_t`. -/
def stepHead : List Instr :=
  [.dp .sub .r11 .r11 (.imm 1), .dp .add .r1 .r0 (.reg .r11), .ldrb .r1 .r1 BITS,
    .dp .eor .r10 .r10 (.reg .r1)] ++ mask ++ cswap X2 X3 ++ cswap Z2 Z3 ++ [.mov .r10 (.reg .r1)]

/-- One iteration of the ladder: `stepHead`, then the formulas of RFC 7748 §5
in order. -/
def step : Prog isa :=
  .seq (.block stepHead) <|
  .seq (.block (add A X2 Z2)) <| .seq (mul AA A A) <| .seq (.block (sub B X2 Z2)) <|
  .seq (mul BB B B) <| .seq (.block (sub E AA BB)) <| .seq (.block (add C X3 Z3)) <|
  .seq (.block (sub D X3 Z3)) <| .seq (mul DA D A) <| .seq (mul CB C B) <|
  .seq (.block (add X3 DA CB)) <| .seq (mul X3 X3 X3) <| .seq (.block (sub Z3 DA CB)) <|
  .seq (mul Z3 Z3 Z3) <| .seq (mul Z3 X1 Z3) <| .seq (mul X2 AA BB) <| .seq (mul Z2 A24 E) <|
  .seq (.block (add Z2 AA Z2)) <| .seq (mul Z2 E Z2) (.block [.cmp .r11 (.imm 0)])

/-- The 255 iterations, for `t` from 254 down to 0, with `swap = 0`. -/
def ladder : Prog isa :=
  .seq (.block [.mov .r11 (.imm 255), .mov .r10 (.imm 0)]) (.loop step .ne)

/-- The swap after the loop. -/
def lastSwap : List Instr := mask ++ cswap X2 X3 ++ cswap Z2 Z3

/-! ## Inversion

`[R] = [Z2]^(p-2)`, square-and-multiply over the bits of `p - 2` from 254
down to 0 (`t = r10 - 1`): `R = R²`, then `R = R · Z2` unless `t` is 4 or 2. -/

/-- `[R] = 1`. -/
def one : List Instr :=
  [.mov .r1 (.imm 1), .mov .r2 (.imm 0), .str .r1 .r0 R] ++ storeN .r2 (R + 4) 15

def invStep : Prog isa :=
  .seq (.block [.dp .sub .r10 .r10 (.imm 1)]) <| .seq (mul R R R) <|
  .seq (.block [.cmp .r10 (.imm 4)]) <|
  .seq (.ite .eq (.block []) (.seq (.block [.cmp .r10 (.imm 2)]) (.ite .eq (.block []) (mul R R Z2))))
    (.block [.cmp .r10 (.imm 0)])

def invert : Prog isa := .seq (.block (one ++ [.mov .r10 (.imm 255)])) (.loop invStep .ne)

/-! ## Encoding and decoding -/

/-- `r3` modulo `2¹⁵`. -/
def low15 : List Instr := [.mov .r3 (.shifted .r3 .lsl 17), .mov .r3 (.shifted .r3 .lsr 17)]

/-- Bit 255 of `[X2]` cleared, and 19 times it into `r5` (the mask of a limb in
`r6`). -/
def freezeA : List Instr :=
  [.movw .r6 0xffff, .ldr .r3 .r0 (X2 + 60), .mov .r5 (.shifted .r3 .lsr 15)] ++ low15 ++
  [.str .r3 .r0 (X2 + 60), .mov .r2 (.imm 19), .mul .r5 .r5 .r2]

/-- The mask `-(bit 255 of [Y])` into `r9`, and bit 255 of `[Y]` cleared. -/
def freezeB : List Instr :=
  [.ldr .r3 .r0 (Y + 60), .mov .r9 (.shifted .r3 .lsr 15), .mov .r1 (.imm 0),
    .dp .sub .r9 .r1 (.reg .r9)] ++ low15 ++ [.str .r3 .r0 (Y + 60)]

/-- Limb `k` of `[X2]`, or of `[Y]` if the mask `r9` is all ones, as bytes
`2k` and `2k + 1` of `out` (`r12`). -/
def outStep (k : Nat) : List Instr :=
  [.ldr .r2 .r0 (X2 + 4 * k), .ldr .r3 .r0 (Y + 4 * k), .dp .eor .r3 .r3 (.reg .r2),
    .dp .and .r3 .r3 (.reg .r9), .dp .eor .r2 .r2 (.reg .r3), .strb .r2 .r12 (2 * k),
    .mov .r2 (.shifted .r2 .lsr 8), .strb .r2 .r12 (2 * k + 1)]

/-- `[X2]` reduced fully, into `out` (`r12`): bit 255 folded in as 19, then
`y = x + 19` into `Y`, and `y - 2²⁵⁵` selected (with the mask `r9`) if
bit 255 of `y` is set. -/
def freeze : List Instr :=
  freezeA ++ pass .r0 X2 (ldSrc X2) ++ [.mov .r5 (.imm 19)] ++ pass .r0 Y (ldSrc X2) ++ freezeB ++
    (List.range 16).flatMap outStep

/-- The callee-saved registers we use, saved at `4i` of the working space. -/
def savedReg : Nat → Reg
  | 0 => .r4 | 1 => .r5 | 2 => .r6 | 3 => .r7 | 4 => .r8 | 5 => .r9 | 6 => .r10 | _ => .r11

/-- Limb `k` of `u` (bytes `2k` and `2k + 1` at `r2`, the top bit masked) into
`X1` and `X3`. -/
def decodeStep (k : Nat) : List Instr :=
  [.ldrb .r4 .r2 (2 * k), .ldrb .r5 .r2 (2 * k + 1)] ++
    (if k = 15 then [.dp .and .r5 .r5 (.imm 127)] else []) ++
    [.dp .add .r4 .r4 (.shifted .r5 .lsl 8), .str .r4 .r0 (X1 + 4 * k), .str .r4 .r0 (X3 + 4 * k)]

/-- `x2 = 1`, `z2 = 0`, `z3 = 1` and `A24 = 121665 = 0xdb41 + 2¹⁶`. -/
def consts : List Instr :=
  [.mov .r4 (.imm 1), .mov .r5 (.imm 0), .movw .r6 0xdb41, .str .r4 .r0 X2, .str .r5 .r0 Z2,
    .str .r4 .r0 Z3, .str .r6 .r0 A24, .str .r4 .r0 (A24 + 4)] ++
  storeN .r5 (X2 + 4) 15 ++ storeN .r5 (Z2 + 4) 15 ++ storeN .r5 (Z3 + 4) 15 ++ storeN .r5 (A24 + 8) 14

/-- Saves the registers (with the working space in `r3`), then `out` into
`r12` and the working space into `r0`, the u-coordinate into `X1` and `X3`,
and the constants. -/
def setup : List Instr :=
  (List.range 8).flatMap (fun i => [.str (savedReg i) .r3 (4 * i)]) ++
  [.mov .r12 (.reg .r0), .mov .r0 (.reg .r3)] ++ (List.range 16).flatMap decodeStep ++ consts

/-- The bits of the byte at `r1` into `BITS` at `r6`, advancing both. -/
def bitsBody : List Instr :=
  [.ldrb .r4 .r1 0] ++
  (List.range 8).flatMap (fun j =>
    (if j = 0 then [.dp .and .r5 .r4 (.imm 1)]
     else [.mov .r5 (.shifted .r4 .lsr j), .dp .and .r5 .r5 (.imm 1)]) ++ [.strb .r5 .r6 (BITS + j)]) ++
  [.dp .add .r1 .r1 (.imm 1), .dp .add .r6 .r6 (.imm 8), .subs .r7 .r7 (.imm 1)]

/-- `BITS[8i + j] = bit j of scalar[i]`, then the clamping: bits 0, 1 and 2
cleared and bit 254 set. -/
def bits : Prog isa :=
  .seq (.block [.mov .r6 (.reg .r0), .mov .r7 (.imm 32)])
    (.seq (.loop (.block bitsBody) .ne)
      (.block [.mov .r5 (.imm 0), .strb .r5 .r0 BITS, .strb .r5 .r0 (BITS + 1),
        .strb .r5 .r0 (BITS + 2), .mov .r5 (.imm 1), .strb .r5 .r0 (BITS + 254)]))

def restore : List Instr := (List.range 8).flatMap fun i => [.ldr (savedReg i) .r0 (4 * i)]

def x25519 : Prog isa :=
  .seq (.block setup) <| .seq bits <| .seq ladder <| .seq (.block lastSwap) <|
    .seq invert <| .seq (mul X2 X2 R) (.block (freeze ++ restore))

end VG.Impl.X25519.Arm
