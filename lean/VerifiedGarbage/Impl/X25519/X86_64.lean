import VerifiedGarbage.TCB.X86_64.Isa

/-!
# X25519: x86-64 implementation

`vg_x25519(out = rdi, scalar = rsi, point = rdx, scratch = rcx)`.

A field element is four 64-bit words `x0 + 2⁶⁴ x1 + 2¹²⁸ x2 + 2¹⁹² x3`,
any number below `2²⁵⁶`, standing for its residue modulo `p = 2²⁵⁵ - 19`;
only the result is reduced fully. Every element lives in the working space,
at a constant offset from its base, which is in `rdi` once the arguments are
read (`out` then in `rsi`):

* `[0, 48)`: the saved `rbx, rbp, r12–r15`;
* `x1, x2, z2, x3, z3` and the ladder's temporaries, 32 bytes each (`X1`, …);
* `swap` (a word, 0 or 1) and the bits of the clamped scalar `k` (`BITS`,
  byte `t` is bit `t` of `k`).

The arithmetic (registers `rax, rdx, rcx, rbp, r8–r15`):

* `mul`: the 512-bit product, row by row (`r8–r15`, with the carry of a row
  in `rbp`), then `lo + 38 hi` (as `2²⁵⁶ ≡ 38`), whose carry word `c` is
  folded in as `38 c`, and a last carry of that as 38 more;
* `add`, `sub`: with carries (borrows), each carry folded in (subtracted) as
  38, twice;
* `mulSmall`: by a one-word constant (`a24`), folded as for `mul`;
* `cswap`: with the mask `-swap`, as RFC 7748 §5 describes;
* `freeze`: the full reduction of the result, by folding bit 255 in as 19,
  then selecting `x + 19 - 2²⁵⁵` with a mask if it is not negative.

The ladder follows RFC 7748 §5 operation by operation, over the bits of `k`
from 254 down to 0 (the counter `rbx`, which indexes `BITS`), and the
inversion `z2^(p-2)` is the addition chain of ref10 (254 squarings, each a
`mul`, and 11 multiplications).

The only branches are on the loop counters, and every address is a pointer
plus a constant or a counter, so only the pointers can affect timing.
-/

namespace VG.Impl.X25519.X86_64

open VG.X86_64

/-- `[b + d]`. -/
def at_ (b : Reg) (d : Nat) : MemOp := { base := b, disp := d }

/-- `[rdi + d]`: byte `d` of the working space. -/
def sc (d : Nat) : MemOp := at_ .rdi d

/-! ## The layout of the working space -/

def X1 : Nat := 64
def X2 : Nat := 96
def Z2 : Nat := 128
def X3 : Nat := 160
def Z3 : Nat := 192
def A : Nat := 224
def B : Nat := 256
def C : Nat := 288
def D : Nat := 320
def AA : Nat := 352
def BB : Nat := 384
def E : Nat := 416
def DA : Nat := 448
def CB : Nat := 480
def T0 : Nat := 512
def T1 : Nat := 544
def T2 : Nat := 576
def T3 : Nat := 608
def SWAP : Nat := 640
def BITS : Nat := 768

/-- The words of a product, lowest first. -/
def T : List Reg := [.r8, .r9, .r10, .r11, .r12, .r13, .r14, .r15]

/-- `T[i]`. -/
def t (i : Nat) : Reg := T.getD i .r8

/-! ## Field arithmetic -/

/-- `t:c = t + c + ai · src` (a multiply-accumulate step; it never
overflows). -/
def mulStep (t c ai : Reg) (src : Src) : List Instr :=
  [.mov .rax src, .mul ai, .alu .add .rax (.reg c), .alu .adc .rdx (.imm 0),
    .alu .add t (.reg .rax), .alu .adc .rdx (.imm 0), .mov c (.reg .rdx)]

/-- `r8–r11 = 0`. -/
def zero4 : List Instr := [.mov32 .r8 (.imm 0), .mov32 .r9 (.imm 0), .mov32 .r10 (.imm 0),
  .mov32 .r11 (.imm 0)]

/-- Row `i` of a product: `t[i..i+4] += a_i · b`, `a_i` from `[rdi + a + 8i]`,
`b` from `[rdi + b]`. -/
def row (a b i : Nat) : List Instr :=
  [.mov .rcx (.mem (sc (a + 8 * i))), .mov32 .rbp (.imm 0)] ++
    ((List.range 4).flatMap fun j => mulStep (t (i + j)) .rbp .rcx (.mem (sc (b + 8 * j)))) ++
    [.mov (t (i + 4)) (.reg .rbp)]

/-- `r8–r11 += rax`, with the carry out folded in as 38 (which cannot carry
again). -/
def carry38 : List Instr :=
  [.alu .add .r8 (.reg .rax), .alu .adc .r9 (.imm 0), .alu .adc .r10 (.imm 0),
    .alu .adc .r11 (.imm 0), .alu .sbb .rax (.reg .rax), .alu .and .rax (.imm 38),
    .alu .add .r8 (.reg .rax)]

/-- `r8–r11 += 38 rbp`, with `rcx = 38`. -/
def fold : List Instr := [.mov .rax (.reg .rbp), .mul .rcx] ++ carry38

/-- `[rdi + o] = a, b, c, d`. -/
def stores (o : Nat) (a b c d : Reg) : List Instr :=
  [.store (sc o) a, .store (sc (o + 8)) b, .store (sc (o + 16)) c, .store (sc (o + 24)) d]

/-- `[rdi + o] = r8–r11`. -/
def store4 (o : Nat) : List Instr := stores o .r8 .r9 .r10 .r11

/-- `a, b, c, d = [rdi + o]`. -/
def loads (o : Nat) (a b c d : Reg) : List Instr :=
  [.mov a (.mem (sc o)), .mov b (.mem (sc (o + 8))), .mov c (.mem (sc (o + 16))),
    .mov d (.mem (sc (o + 24)))]

/-- `r8–r11 = r8–r11 + 38 r12–r15` with the carry word in `rbp`, folded. -/
def reduce : List Instr :=
  [.mov32 .rcx (.imm 38), .mov32 .rbp (.imm 0)] ++
    ((List.range 4).flatMap fun j => mulStep (t j) .rbp .rcx (.reg (t (4 + j)))) ++ fold

/-- `[o] = [a] · [b]` (`o` may be `a` or `b`). -/
def mul (o a b : Nat) : List Instr :=
  zero4 ++ row a b 0 ++ row a b 1 ++ row a b 2 ++ row a b 3 ++ reduce ++ store4 o

/-- `[o] = k · [a]`, for a constant `k < 2³¹`. -/
def mulSmall (o a : Nat) (k : BitVec 32) : List Instr :=
  zero4 ++ [.mov32 .rcx (.imm k), .mov32 .rbp (.imm 0)] ++
    ((List.range 4).flatMap fun j => mulStep (t j) .rbp .rcx (.mem (sc (a + 8 * j)))) ++
    [.mov32 .rcx (.imm 38)] ++ fold ++ store4 o

/-- `[o] = [a] + [b]`. -/
def add (o a b : Nat) : List Instr :=
  [.mov .r8 (.mem (sc a)), .alu .add .r8 (.mem (sc b)),
    .mov .r9 (.mem (sc (a + 8))), .alu .adc .r9 (.mem (sc (b + 8))),
    .mov .r10 (.mem (sc (a + 16))), .alu .adc .r10 (.mem (sc (b + 16))),
    .mov .r11 (.mem (sc (a + 24))), .alu .adc .r11 (.mem (sc (b + 24))),
    .alu .sbb .rax (.reg .rax), .alu .and .rax (.imm 38)] ++ carry38 ++ store4 o

/-- `[o] = [a] - [b]`: a borrow out is `2²⁵⁶ ≡ 38` too many, subtracted
(twice at most). -/
def sub (o a b : Nat) : List Instr :=
  [.mov .r8 (.mem (sc a)), .alu .sub .r8 (.mem (sc b)),
    .mov .r9 (.mem (sc (a + 8))), .alu .sbb .r9 (.mem (sc (b + 8))),
    .mov .r10 (.mem (sc (a + 16))), .alu .sbb .r10 (.mem (sc (b + 16))),
    .mov .r11 (.mem (sc (a + 24))), .alu .sbb .r11 (.mem (sc (b + 24))),
    .alu .sbb .rax (.reg .rax), .alu .and .rax (.imm 38),
    .alu .sub .r8 (.reg .rax), .alu .sbb .r9 (.imm 0), .alu .sbb .r10 (.imm 0),
    .alu .sbb .r11 (.imm 0), .alu .sbb .rax (.reg .rax), .alu .and .rax (.imm 38),
    .alu .sub .r8 (.reg .rax)] ++ store4 o

/-- Swaps `[x]` and `[y]` if the mask `rcx` is all ones (and not if it is
zero): both into `r8–r11` and `r12–r15`, then `d = rcx ∧ (x ⊕ y)`, `x ⊕= d`,
`y ⊕= d`, word by word (with `d` in `rax`), and both stored back. -/
def cswap (x y : Nat) : List Instr :=
  loads x .r8 .r9 .r10 .r11 ++ loads y .r12 .r13 .r14 .r15 ++
  ([(Reg.r8, Reg.r12), (.r9, .r13), (.r10, .r14), (.r11, .r15)].flatMap fun (a, b) =>
    [.mov .rax (.reg a), .alu .xor .rax (.reg b), .alu .and .rax (.reg .rcx),
      .alu .xor a (.reg .rax), .alu .xor b (.reg .rax)]) ++
  store4 x ++ stores y .r12 .r13 .r14 .r15

/-- `[o] = [a]^(2^n)`, for `n ≥ 2`: a square, then `n - 1` in place. -/
def sqn (o a n : Nat) : Prog isa :=
  .seq (.block (mul o a a ++ [.mov32 .rbx (.imm (BitVec.ofNat 32 (n - 1)))]))
    (.loop (.block (mul o o o ++ [.alu .sub .rbx (.imm 1)])) .ne)

/-! ## The ladder -/

/-- The ladder's `a24 = 121665`. -/
def a24 : BitVec 32 := 121665

/-- One iteration of the ladder, for the bit `t = rbx - 1`: `k_t` from
`BITS`, `swap ^= k_t` into the mask `rcx = -swap`, the swaps, `swap = k_t`,
and the formulas of RFC 7748 §5 in order. -/
def step : List Instr :=
  [.alu .sub .rbx (.imm 1), .movzx8 .rax { base := .rdi, index := some .rbx, disp := BITS },
    .mov .rdx (.mem (sc SWAP)), .alu .xor .rdx (.reg .rax), .store (sc SWAP) .rax,
    .mov32 .rcx (.imm 0), .alu .sub .rcx (.reg .rdx)] ++
  cswap X2 X3 ++ cswap Z2 Z3 ++
  add A X2 Z2 ++ mul AA A A ++ sub B X2 Z2 ++ mul BB B B ++ sub E AA BB ++
  add C X3 Z3 ++ sub D X3 Z3 ++ mul DA D A ++ mul CB C B ++
  add X3 DA CB ++ mul X3 X3 X3 ++ sub Z3 DA CB ++ mul Z3 Z3 Z3 ++ mul Z3 X1 Z3 ++
  mul X2 AA BB ++ mulSmall Z2 E a24 ++ add Z2 AA Z2 ++ mul Z2 E Z2 ++
  [.alu .test .rbx (.reg .rbx)]

/-- The 255 iterations, for `t` from 254 down to 0. -/
def ladder : Prog isa :=
  .seq (.block [.mov32 .rbx (.imm 255)]) (.loop (.block step) .ne)

/-- `[rdi + 8 rbx + BITS + j]`: bit `j` of byte `rbx` of the scalar. -/
def bitAt (j : Nat) : MemOp :=
  { base := .rdi, index := some .rbx, scale := 8, disp := ((BITS + j : Nat) : Int) }

/-- `BITS[8i + j] = bit j of scalar[i]`, for the 32 bytes `i` (the counter
`rbx`) of the scalar at `rsi`; then the clamped bits: `BITS[0..2] = 0` and
`BITS[254] = 1` (RFC 7748 §5, `decodeScalar25519`). -/
def bits : Prog isa :=
  .seq (.block [.mov32 .rbx (.imm 0)]) (.seq (.loop (.block (
    [.movzx8 .rax { base := .rsi, index := some .rbx }] ++
    ((List.range 8).flatMap fun j =>
      [.mov .rdx (.reg .rax)] ++ (if j = 0 then [] else [.shift .shr .rdx j]) ++
      [.alu .and .rdx (.imm 1),
        .store8 (bitAt j) .rdx]) ++
    [.alu .add .rbx (.imm 1), .alu .cmp .rbx (.imm 32)])) .ne)
    (.block [.mov32 .rax (.imm 0), .store8 (sc BITS) .rax, .store8 (sc (BITS + 1)) .rax,
      .store8 (sc (BITS + 2)) .rax, .mov32 .rax (.imm 1), .store8 (sc (BITS + 254)) .rax]))

/-! ## Inversion

`[T1] = [Z2]^(p-2)`, `p - 2 = 2²⁵⁵ - 21`, as ref10's `fe_invert`. -/

def invert : Prog isa :=
  .seq (.block (mul T0 Z2 Z2)) <|                           -- z^2
  .seq (.block (mul T1 T0 T0 ++ mul T1 T1 T1)) <|           -- z^8
  .seq (.block (mul T1 Z2 T1 ++ mul T0 T0 T1 ++             -- z^9, z^11
    mul T2 T0 T0 ++ mul T1 T1 T2)) <|                       -- z^22, z^(2^5 - 1)
  .seq (sqn T2 T1 5) <| .seq (.block (mul T1 T2 T1)) <|      -- z^(2^10 - 1)
  .seq (sqn T2 T1 10) <| .seq (.block (mul T2 T2 T1)) <|     -- z^(2^20 - 1)
  .seq (sqn T3 T2 20) <| .seq (.block (mul T2 T3 T2)) <|     -- z^(2^40 - 1)
  .seq (sqn T2 T2 10) <| .seq (.block (mul T1 T2 T1)) <|     -- z^(2^50 - 1)
  .seq (sqn T2 T1 50) <| .seq (.block (mul T2 T2 T1)) <|     -- z^(2^100 - 1)
  .seq (sqn T3 T2 100) <| .seq (.block (mul T2 T3 T2)) <|    -- z^(2^200 - 1)
  .seq (sqn T2 T2 50) <| .seq (.block (mul T1 T2 T1)) <|     -- z^(2^250 - 1)
  .seq (sqn T1 T1 5) (.block (mul T1 T1 T0))                -- z^(2^255 - 21)

/-! ## Encoding and decoding -/

/-- `2⁶³ - 1`. -/
def low63 : BitVec 64 := 0x7fffffffffffffff

/-- The fully reduced `[a]` (`< p`) into `r8–r11`: bit 255 folded in as 19
(`x < 2²⁵⁵ + 19`), then `x + 19 - 2²⁵⁵` selected if it is not negative. -/
def freeze (a : Nat) : List Instr :=
  [.mov .r8 (.mem (sc a)), .mov .r9 (.mem (sc (a + 8))), .mov .r10 (.mem (sc (a + 16))),
    .mov .r11 (.mem (sc (a + 24))),
    .mov .rax (.reg .r11), .shift .shr .rax 63, .movImm64 .rdx low63, .alu .and .r11 (.reg .rdx),
    .mov32 .rcx (.imm 0), .alu .sub .rcx (.reg .rax), .alu .and .rcx (.imm 19),
    .alu .add .r8 (.reg .rcx), .alu .adc .r9 (.imm 0), .alu .adc .r10 (.imm 0),
    .alu .adc .r11 (.imm 0),
    .mov .r12 (.reg .r8), .alu .add .r12 (.imm 19), .mov .r13 (.reg .r9), .alu .adc .r13 (.imm 0),
    .mov .r14 (.reg .r10), .alu .adc .r14 (.imm 0), .mov .r15 (.reg .r11),
    .alu .adc .r15 (.imm 0),
    .mov .rax (.reg .r15), .shift .shr .rax 63, .alu .and .r15 (.reg .rdx),
    .mov32 .rcx (.imm 0), .alu .sub .rcx (.reg .rax)] ++
  ([(Reg.r8, Reg.r12), (.r9, .r13), (.r10, .r14), (.r11, .r15)].flatMap fun (x, y) =>
    [.alu .xor y (.reg x), .alu .and y (.reg .rcx), .alu .xor x (.reg y)])

/-- The callee-saved registers we use, and where they are saved. -/
def saved : List (Reg × Nat) :=
  [(.rbx, 0), (.rbp, 8), (.r12, 16), (.r13, 24), (.r14, 32), (.r15, 40)]

/-- Saves them (with the working space in `rcx`). -/
def save : List Instr := saved.map fun (r, d) => .store (at_ .rcx d) r

def restore : List Instr := saved.map fun (r, d) => .mov r (.mem (sc d))

/-- The u-coordinate at `rdx`, its top bit masked, into `r8–r11`. -/
def loadU : List Instr :=
  [.mov .r8 (.mem (at_ .rdx 0)), .mov .r9 (.mem (at_ .rdx 8)), .mov .r10 (.mem (at_ .rdx 16)),
    .mov .r11 (.mem (at_ .rdx 24)), .movImm64 .rax low63, .alu .and .r11 (.reg .rax)]

/-- Reads the arguments (with the working space in `rcx`): `u` with its top
bit masked into `X1` and `X3`; then `out` into `r12`, the working space into
`rdi`, and `x2 = 1`, `z2 = 0`, `z3 = 1`, `swap = 0`. The scalar stays at
`rsi` for `bits`. -/
def setup : List Instr :=
  loadU ++ save ++ [.mov .r12 (.reg .rdi), .mov .rdi (.reg .rcx)] ++ store4 X1 ++ store4 X3 ++
    [.mov32 .rax (.imm 0), .mov32 .rdx (.imm 1)] ++ stores X2 .rdx .rax .rax .rax ++
    stores Z2 .rax .rax .rax .rax ++ stores Z3 .rdx .rax .rax .rax ++ [.store (sc SWAP) .rax]

/-- `x2 · z2^(p-2)`, reduced fully, to `out`, and the saved registers
restored (before the stores, which do not touch the working space). -/
def finish : List Instr :=
  mul X2 X2 T1 ++ freeze X2 ++ restore ++
  [.store (at_ .rsi 0) .r8, .store (at_ .rsi 8) .r9, .store (at_ .rsi 16) .r10,
    .store (at_ .rsi 24) .r11]

/-- The swap after the loop. -/
def lastSwap : List Instr :=
  [.mov .rdx (.mem (sc SWAP)), .mov32 .rcx (.imm 0), .alu .sub .rcx (.reg .rdx)] ++
  cswap X2 X3 ++ cswap Z2 Z3

def x25519 : Prog isa :=
  .seq (.block setup) <| .seq bits <| .seq (.block [.mov .rsi (.reg .r12)]) <| .seq ladder <|
    .seq (.block lastSwap) <| .seq invert (.block finish)

end VG.Impl.X25519.X86_64
