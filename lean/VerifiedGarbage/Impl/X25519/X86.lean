import VerifiedGarbage.TCB.X86.Isa

/-!
# X25519: x86 (32-bit) implementation

`vg_x25519(out, scalar, point, scratch)`: every argument is on the stack
(cdecl), at `[esp + 4]`, …, `[esp + 16]` on entry, and no code here moves
`esp`, so they stay there.

A field element is eight 32-bit words `x0 + 2³² x1 + … + 2²²⁴ x7`, any
number below `2²⁵⁶`, standing for its residue modulo `p = 2²⁵⁵ - 19`; only
the result is reduced fully. Every element lives in the working space, at a
constant offset from its base, which is in `edi` once the arguments are read:

* `[0, 16)`: the saved `ebx, esi, edi, ebp`;
* `[16, 20)`: `swap` (0 or 1);
* `[32, 288)`: the bits of the scalar (byte `t` is bit `t` of the clamped
  scalar, for `t < 255`);
* from `288`: `x1, x2, z2, x3, z3` and the ladder's temporaries, 32 bytes
  each (`X1`, …), then a 64-byte product (`T`).

The arithmetic sums *columns*: a column is a sum of *terms* (products of two
words, words, complemented words and constants), each added to a 96-bit
accumulator `ebx + 2³² ecx + 2⁶⁴ ebp`, after which its low word is stored
and the accumulator shifted down by a word (`column`). An operation's
columns sum a multiple-word number from its operands (`cols`); then its top
carry `c` is folded in as `38 c` (`fold`, as `2²⁵⁶ ≡ 38`), and a last
carry of that as 38 more, which cannot carry again. So:

* `mul`: the 512-bit product by columns (product scanning) into `T`, then
  `lo + 38 hi` (`linear`);
* `add`: `a + b`; `sub`: `a + (2²⁵⁶ - 1 - b) + (2²⁵⁶ - 75) = a - b + 4p`, so
  that every term is a natural number; `mulSmall`: `121665 a`;
* `cswap`: with the mask `-swap`, as RFC 7748 §5 describes;
* `freeze`: the full reduction of the result, by folding bit 255 in as 19,
  then selecting `x + 19 - 2²⁵⁵` with a mask if it is not negative.

The ladder follows RFC 7748 §5 operation by operation, over the bits of the
scalar from 254 down to 0 (the counter `esi` is `t + 1`), and the inversion
`z2^(p-2)` is the addition chain of ref10 (254 squarings and 11
multiplications, each squaring a `mul`), its runs of squarings loops with
the counter `esi`.

The only branches are on the loop counters, and every address is a pointer
plus a constant, or `edi` plus the counter, so only the pointers can affect
timing.
-/

namespace VG.Impl.X25519.X86

open VG.X86

/-- `[b + d]`. -/
def at_ (b : Reg) (d : Nat) : MemOp := { base := b, disp := d }

/-- `[edi + d]`: byte `d` of the working space. -/
def sc (d : Nat) : MemOp := at_ .edi d

/-! ## The layout of the working space -/

def SWAP : Nat := 16
def BITS : Nat := 32
def X1 : Nat := 288
def X2 : Nat := 320
def Z2 : Nat := 352
def X3 : Nat := 384
def Z3 : Nat := 416
def A : Nat := 448
def B : Nat := 480
def C : Nat := 512
def D : Nat := 544
def AA : Nat := 576
def BB : Nat := 608
def E : Nat := 640
def DA : Nat := 672
def CB : Nat := 704
def T0 : Nat := 736
def T1 : Nat := 768
def T2 : Nat := 800
def T3 : Nat := 832
/-- The 16 words of a product. -/
def T : Nat := 864

/-! ## Columns -/

/-- A term of a column. -/
inductive Term
  /-- The product of the words at `[edi + x]` and `[edi + y]`. -/
  | mulM (x y : Nat)
  /-- The product of the word at `[edi + x]` and a constant. -/
  | mulI (x : Nat) (c : BitVec 32)
  /-- The word at `[edi + x]`. -/
  | addM (x : Nat)
  /-- A constant. -/
  | addI (c : BitVec 32)
  /-- The complement `2³² - 1 - w` of the word `w` at `[edi + x]`. -/
  | addNot (x : Nat)
  deriving DecidableEq, Repr

/-- `ebx:ecx:ebp += eax`, and more generally `+= src` (`eax` and `edx` aside). -/
def accAdd (src : Src) : List Instr :=
  [.alu .add .ebx src, .alu .adc .ecx (.imm 0), .alu .adc .ebp (.imm 0)]

/-- `ebx:ecx:ebp += eax · src`. -/
def accMul (src : Src) : List Instr :=
  [.mov .edx src, .mul .edx, .alu .add .ebx (.reg .eax), .alu .adc .ecx (.reg .edx),
    .alu .adc .ebp (.imm 0)]

/-- Adding a term to the accumulator. -/
def Term.code : Term → List Instr
  | .mulM x y => .mov .eax (.mem (sc x)) :: accMul (.mem (sc y))
  | .mulI x c => .mov .eax (.mem (sc x)) :: accMul (.imm c)
  | .addM x => accAdd (.mem (sc x))
  | .addI c => accAdd (.imm c)
  | .addNot x => [.mov .eax (.mem (sc x)), .alu .xor .eax (.imm 0xffffffff)] ++ accAdd (.reg .eax)

/-- The accumulator's low word stored at `[edi + o]`, and the accumulator
shifted down by a word. -/
def colEnd (o : Nat) : List Instr :=
  [.store (sc o) .ebx, .mov .ebx (.reg .ecx), .mov .ecx (.reg .ebp), .mov .ebp (.imm 0)]

/-- A column: its terms summed into the accumulator, then its word stored at
`[edi + o]`. -/
def column (ts : List Term) (o : Nat) : List Instr := ts.flatMap Term.code ++ colEnd o

/-- `n` columns, the terms `ts k` of column `k` stored at `[edi + o + 4k]`. -/
def cols (o n : Nat) (ts : Nat → List Term) : List Instr :=
  (List.range n).flatMap fun k => column (ts k) (o + 4 * k)

/-- The accumulator cleared. -/
def zeroAcc : List Instr := [.mov .ebx (.imm 0), .mov .ecx (.imm 0), .mov .ebp (.imm 0)]

/-- The carry `c` in the accumulator (with `38 c < 2³²`) folded into the
element at `[edi + o]` as `38 c`, and its carry out as 38 more. -/
def fold (o : Nat) : List Instr :=
  [.mov .eax (.imm 38), .mul .ebx, .mov .ebx (.reg .eax)] ++
  cols o 8 (fun k => [.addM (o + 4 * k)]) ++
  [.mov .eax (.imm 38), .mul .ebx, .alu .add .eax (.mem (sc o)), .store (sc o) .eax]

/-- An element at `[edi + o]` summed by eight columns, then folded. -/
def linear (o : Nat) (ts : Nat → List Term) : List Instr :=
  zeroAcc ++ cols o 8 ts ++ fold o

/-! ## Field arithmetic -/

/-- The products `a_i b_j` with `i + j = k`. -/
def prodTerms (a b k : Nat) : List Term :=
  ((List.range 8).filter fun i => i ≤ k && k - i < 8).map fun i => .mulM (a + 4 * i) (b + 4 * (k - i))

/-- `[o] = [a] · [b]` (`o` may be `a` or `b`). -/
def mul (o a b : Nat) : List Instr :=
  zeroAcc ++ cols T 16 (prodTerms a b) ++
  linear o (fun k => [.mulI (T + 32 + 4 * k) 38, .addM (T + 4 * k)])

/-- `[o] = 121665 · [a]`. -/
def mulSmall (o a : Nat) : List Instr :=
  linear o (fun k => [.mulI (a + 4 * k) 121665])

/-- `[o] = [a] + [b]`. -/
def add (o a b : Nat) : List Instr :=
  linear o (fun k => [.addM (a + 4 * k), .addM (b + 4 * k)])

/-- The words of `2²⁵⁶ - 75`. -/
def subK (k : Nat) : BitVec 32 := if k = 0 then 0xffffffb5 else 0xffffffff

/-- `[o] = [a] - [b]`, as `[a] + (2²⁵⁶ - 1 - [b]) + (2²⁵⁶ - 75) = [a] - [b] + 4p`. -/
def sub (o a b : Nat) : List Instr :=
  linear o (fun k => [.addM (a + 4 * k), .addNot (b + 4 * k), .addI (subK k)])

/-- `[o] = [a]`. -/
def copy (o a : Nat) : List Instr :=
  (List.range 8).flatMap fun k => [.mov .eax (.mem (sc (a + 4 * k))), .store (sc (o + 4 * k)) .eax]

/-- Swaps `[x]` and `[y]` if the mask `ecx` is all ones (and not if it is
zero): `d = ecx ∧ (x ⊕ y)`, `x ⊕= d`, `y ⊕= d`, word by word. -/
def cswap (x y : Nat) : List Instr :=
  (List.range 8).flatMap fun k =>
    [.mov .eax (.mem (sc (x + 4 * k))), .mov .edx (.mem (sc (y + 4 * k))), .mov .ebx (.reg .eax),
      .alu .xor .ebx (.reg .edx), .alu .and .ebx (.reg .ecx), .alu .xor .eax (.reg .ebx),
      .alu .xor .edx (.reg .ebx), .store (sc (x + 4 * k)) .eax, .store (sc (y + 4 * k)) .edx]

/-- A field operation, by its output and inputs. -/
inductive Op
  | mul (o a b : Nat)
  | mulSmall (o a : Nat)
  | add (o a b : Nat)
  | sub (o a b : Nat)
  | copy (o a : Nat)
  deriving DecidableEq, Repr

def Op.code : Op → List Instr
  | .mul o a b => X86.mul o a b
  | .mulSmall o a => X86.mulSmall o a
  | .add o a b => X86.add o a b
  | .sub o a b => X86.sub o a b
  | .copy o a => X86.copy o a

/-- A sequence of operations. -/
def ops (l : List Op) : List Instr := l.flatMap Op.code

/-- `[o] = [o]^(2^n)`, for `n ≥ 1`: `n` squarings, counted by `esi`. -/
def sqn (o n : Nat) : Prog isa :=
  .seq (.block [.mov .esi (.imm (BitVec.ofNat 32 n))])
    (.loop (.block (mul o o o ++ [.alu .sub .esi (.imm 1)])) .ne)

/-! ## The ladder -/

/-- The operations of one iteration of the ladder, after the swaps (RFC 7748
§5, in order). -/
def stepOps : List Op :=
  [.add A X2 Z2, .mul AA A A, .sub B X2 Z2, .mul BB B B, .sub E AA BB,
    .add C X3 Z3, .sub D X3 Z3, .mul DA D A, .mul CB C B,
    .add X3 DA CB, .mul X3 X3 X3, .sub Z3 DA CB, .mul Z3 Z3 Z3, .mul Z3 X1 Z3,
    .mul X2 AA BB, .mulSmall Z2 E, .add Z2 AA Z2, .mul Z2 E Z2]

/-- The start of an iteration, for the bit `t = esi - 1`: `k_t` from `BITS`
(at `edi + t`), `swap ^= k_t` into the mask `ecx = -swap`, and `swap = k_t`. -/
def stepHead : List Instr :=
  [.alu .sub .esi (.imm 1), .mov .eax (.reg .edi), .alu .add .eax (.reg .esi),
    .movzx8 .eax (at_ .eax BITS), .mov .edx (.mem (sc SWAP)), .alu .xor .edx (.reg .eax),
    .store (sc SWAP) .eax, .mov .ecx (.imm 0), .alu .sub .ecx (.reg .edx)]

/-- One iteration of the ladder. -/
def step : List Instr :=
  stepHead ++ cswap X2 X3 ++ cswap Z2 Z3 ++ ops stepOps ++ [.alu .test .esi (.reg .esi)]

/-- The 255 iterations, for `t` from 254 down to 0. -/
def ladder : Prog isa :=
  .seq (.block [.mov .esi (.imm 255)]) (.loop (.block step) .ne)

/-- The swap after the loop. -/
def lastSwap : List Instr :=
  [.mov .edx (.mem (sc SWAP)), .mov .ecx (.imm 0), .alu .sub .ecx (.reg .edx)] ++
  cswap X2 X3 ++ cswap Z2 Z3

/-! ## Inversion

`[T1] = [Z2]^(p-2)`, `p - 2 = 2²⁵⁵ - 21`, as ref10's `fe_invert`. -/

def invert : Prog isa :=
  .seq (.block (ops [.mul T0 Z2 Z2, .copy T1 T0])) <| .seq (sqn T1 2) <|    -- z^2, z^8
  .seq (.block (ops [.mul T1 Z2 T1, .mul T0 T0 T1, .mul T2 T0 T0,          -- z^9, z^11, z^22
    .mul T1 T1 T2, .copy T2 T1])) <| .seq (sqn T2 5) <|                    -- z^(2^5 - 1)
  .seq (.block (ops [.mul T1 T2 T1, .copy T2 T1])) <| .seq (sqn T2 10) <|  -- z^(2^10 - 1)
  .seq (.block (ops [.mul T2 T2 T1, .copy T3 T2])) <| .seq (sqn T3 20) <|  -- z^(2^20 - 1)
  .seq (.block (ops [.mul T2 T3 T2])) <| .seq (sqn T2 10) <|               -- z^(2^40 - 1)
  .seq (.block (ops [.mul T1 T2 T1, .copy T2 T1])) <| .seq (sqn T2 50) <|  -- z^(2^50 - 1)
  .seq (.block (ops [.mul T2 T2 T1, .copy T3 T2])) <| .seq (sqn T3 100) <| -- z^(2^100 - 1)
  .seq (.block (ops [.mul T2 T3 T2])) <| .seq (sqn T2 50) <|               -- z^(2^200 - 1)
  .seq (.block (ops [.mul T1 T2 T1])) <| .seq (sqn T1 5) <|                -- z^(2^250 - 1)
  .block (ops [.mul T1 T1 T0])                                             -- z^(2^255 - 21)

/-! ## Encoding and decoding -/

/-- `2³¹ - 1`. -/
def low31 : BitVec 32 := 0x7fffffff

/-- The element at `[edi + o]` reduced fully (`< p`), in place: bit 255
folded in as 19 (`x < 2²⁵⁵ + 19`), then `x + 19 - 2²⁵⁵` (computed in `T`)
selected if it is not negative. -/
def freeze (o : Nat) : List Instr :=
  [.mov .eax (.mem (sc (o + 28))), .shift .shr .eax 31, .mov .edx (.imm 19), .mul .edx,
    .mov .ebx (.reg .eax), .mov .ecx (.imm 0), .mov .ebp (.imm 0),
    .mov .eax (.mem (sc (o + 28))), .alu .and .eax (.imm low31), .store (sc (o + 28)) .eax] ++
  cols o 8 (fun k => [.addM (o + 4 * k)]) ++
  [.mov .ebx (.imm 19), .mov .ecx (.imm 0), .mov .ebp (.imm 0)] ++
  cols T 8 (fun k => [.addM (o + 4 * k)]) ++
  [.mov .eax (.mem (sc (T + 28))), .shift .shr .eax 31, .mov .ecx (.imm 0), .alu .sub .ecx (.reg .eax),
    .mov .eax (.mem (sc (T + 28))), .alu .and .eax (.imm low31), .store (sc (T + 28)) .eax] ++
  (List.range 8).flatMap fun k =>
    [.mov .eax (.mem (sc (o + 4 * k))), .mov .edx (.mem (sc (T + 4 * k))), .alu .xor .edx (.reg .eax),
      .alu .and .edx (.reg .ecx), .alu .xor .eax (.reg .edx), .store (sc (o + 4 * k)) .eax]

/-- The callee-saved registers, and where they are saved. -/
def saved : List (Reg × Nat) := [(.ebx, 0), (.esi, 4), (.edi, 8), (.ebp, 12)]

/-- The working space (`[esp + 16]`) into `edi`, saving the callee-saved
registers in it (via `eax`). -/
def save : List Instr :=
  .mov .eax (.mem (at_ .esp 16)) :: saved.map (fun (r, d) => .store (at_ .eax d) r) ++
    [.mov .edi (.reg .eax)]

/-- Restores them (via `eax`, from `edi`, which is restored last). -/
def restore : List Instr :=
  [.mov .eax (.reg .edi), .mov .ebx (.mem (at_ .eax 0)), .mov .esi (.mem (at_ .eax 4)),
    .mov .ebp (.mem (at_ .eax 12)), .mov .edi (.mem (at_ .eax 8))]

/-- The u-coordinate (`[esp + 12]`) with its top bit masked, into `X1`. -/
def loadPoint : List Instr :=
  .mov .esi (.mem (at_ .esp 12)) :: (List.range 8).flatMap fun k =>
    [.mov .eax (.mem (at_ .esi (4 * k)))] ++ (if k = 7 then [.alu .and .eax (.imm low31)] else []) ++
      [.store (sc (X1 + 4 * k)) .eax]

/-- Bit `j` of the byte in `eax` into `BITS + 8i + j`. -/
def bitOf (i j : Nat) : List Instr :=
  [.mov .edx (.reg .eax)] ++ (if j = 0 then [] else [.shift .shr .edx j]) ++
    [.alu .and .edx (.imm 1), .store8 (sc (BITS + 8 * i + j)) .dl]

/-- The bits of the scalar (`[esp + 8]`), clamped: bits 0, 1 and 2 cleared
and bit 254 set. -/
def loadScalar : List Instr :=
  .mov .esi (.mem (at_ .esp 8)) ::
  ((List.range 32).flatMap fun i =>
    .movzx8 .eax (at_ .esi i) :: (List.range 8).flatMap fun j => bitOf i j) ++
  [.mov .edx (.imm 0), .store8 (sc BITS) .dl, .store8 (sc (BITS + 1)) .dl,
    .store8 (sc (BITS + 2)) .dl, .mov .edx (.imm 1), .store8 (sc (BITS + 254)) .dl]

/-- `[o] = c`, for a one-word constant `c`. -/
def setSmall (o : Nat) (c : BitVec 32) : List Instr :=
  (List.range 8).flatMap fun k => [.mov .eax (.imm (if k = 0 then c else 0)), .store (sc (o + 4 * k)) .eax]

/-- `x3 = x1`, `x2 = 1`, `z2 = 0`, `z3 = 1`, `swap = 0`. -/
def initLadder : List Instr :=
  copy X3 X1 ++ setSmall X2 1 ++ setSmall Z2 0 ++ setSmall Z3 1 ++
    [.mov .eax (.imm 0), .store (sc SWAP) .eax]

def setup : List Instr := save ++ loadPoint ++ loadScalar ++ initLadder

/-- `x2 · z2^(p-2)`, reduced fully, to `out` (`[esp + 4]`), and the saved
registers restored. -/
def finish : List Instr :=
  mul X2 X2 T1 ++ freeze X2 ++
  .mov .esi (.mem (at_ .esp 4)) :: ((List.range 8).flatMap fun k =>
    [.mov .eax (.mem (sc (X2 + 4 * k))), .store (at_ .esi (4 * k)) .eax]) ++
  restore

def x25519 : Prog isa :=
  .seq (.block setup) <| .seq ladder <| .seq (.block lastSwap) <| .seq invert (.block finish)

end VG.Impl.X25519.X86
