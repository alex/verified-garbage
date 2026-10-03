import VerifiedGarbage.TCB.X86_64.Isa

/-!
# X448: x86-64 implementation

`vg_x448(out = rdi, scalar = rsi, point = rdx, scratch = rcx)`.

A field element is seven 64-bit words `x₀ + 2⁶⁴ x₁ + … + 2³⁸⁴ x₆`, any
number below `2⁴⁴⁸`, standing for its residue modulo `p = 2⁴⁴⁸ - 2²²⁴ - 1`;
only the result is reduced fully. Every element lives in the working space,
at a constant offset from its base, which is in `rdi` once the arguments are
read (`out` then in `rsi`):

* `[0, 48)`: the saved `rbx, rbp, r12–r15`; `SWAP` (a word, 0 or 1);
* 22 slots of 64 bytes from byte 64, each holding a field element in its
  first 56 bytes: `x1, x2, z2, x3, z3`, the ladder's temporaries and the
  inversion's;
* `ACC`: the fourteen words of a product;
* `BITS`: the bits of the clamped scalar `k` (byte `t` is bit `t` of `k`).

The arithmetic uses the registers `rax, rcx, rdx, rbp, r8–r15`:

* `mul`: `b` into `r8–r14`, then the product by columns (product scanning:
  column `k` adds every `a_i b_j` with `i + j = k` into a three-word
  accumulator, whose low word is word `k` of the product, stored at `ACC`);
* `sqr`: the same, but each cross product `a_i a_j` (`i < j`) is computed
  once and added twice;
* `reduce`: the product `L + 2⁴⁴⁸ H` (seven words each) becomes
  `L + H + (H - H mod 2²²⁴) + rot(H)`, where `rot(H)` is `H` rotated by 224
  bits, since `2⁴⁴⁸ H ≡ H + 2²²⁴ H` and `2²²⁴ H ≡ (H - H mod 2²²⁴) + rot(H)`
  (as `2⁴⁴⁸ ≡ 2²²⁴ + 1`); the words of `rot(H)`, which are 32 bits off
  `H`'s, are loaded from 4 bytes into `H`'s (but one, whose halves are
  apart in memory). The top word `c` (below 4) is folded in as
  `c + 2²²⁴ c`, twice (`fold`);
* `add`, `sub`: with carries (borrows), each carry folded in (taken out) as
  `1 + 2²²⁴`, twice;
* `mulSmall`: by `a24`, as multiply-accumulate steps, then folded;
* `cswap`: with the mask `-swap`, as RFC 7748 §5 describes;
* `freeze`: the full reduction of the result, `x + 1 + 2²²⁴ - 2⁴⁴⁸` selected
  with a mask if it is not negative (that is, if `x ≥ p`).

The ladder follows RFC 7748 §5 (in another order, `step`), over the bits of `k`
from 447 down to 0 (the counter `rbx`, which indexes `BITS`), and the
inversion `z2^(p-2)` is an addition chain (`Proof/X448/Invert.lean`).

The only branches are on the loop counters, and every address is a pointer
plus a constant or a counter, so only the pointers can affect timing.
-/

namespace VG.Impl.X448.X86_64

open VG.X86_64

/-- `[b + d]`. -/
def at_ (b : Reg) (d : Nat) : MemOp := { base := b, disp := d }

/-- `[rdi + d]`: byte `d` of the working space. -/
def sc (d : Nat) : MemOp := at_ .rdi d

/-! ## The layout of the working space -/

def SWAP : Nat := 48

/-- Each field element occupies the first 56 bytes of a 64-byte slot. -/
def slot (n : Nat) : Nat := 64 + 64 * n
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
def T0 : Nat := slot 14
def T1 : Nat := slot 15
def T2 : Nat := slot 16
def T3 : Nat := slot 17
def T4 : Nat := slot 18
def T5 : Nat := slot 19
def T6 : Nat := slot 20
def T7 : Nat := slot 21
def ACC : Nat := 1536
def BITS : Nat := 2048

/-- The seven words of a field element in registers, lowest first. -/
def W : List Reg := [.r8, .r9, .r10, .r11, .r12, .r13, .r14]

/-- `W[i]`. -/
def w (i : Nat) : Reg := W.getD i .r8

/-! ## Words in registers -/

/-- The registers `rs` loaded with the words at `[rdi + o]`, `[rdi + o + 8]`, … -/
def loads : Nat → List Reg → List Instr
  | _, [] => []
  | o, r :: rs => .mov r (.mem (sc o)) :: loads (o + 8) rs

/-- The registers `rs` stored at `[rdi + o]`, `[rdi + o + 8]`, … -/
def stores : Nat → List Reg → List Instr
  | _, [] => []
  | o, r :: rs => .store (sc o) r :: stores (o + 8) rs

/-- `op` on the first pair, `op'` on the others: an addition (subtraction)
with carries (borrows) along the words. -/
def chain (op op' : AluOp) : List Reg → List Src → List Instr
  | r :: rs, s :: ss => .alu op r s :: chain op' op' rs ss
  | _, _ => []

/-- The words of `[o]`. -/
def words (o : Nat) : List Src := (List.range 7).map fun i => .mem (sc (o + 8 * i))

/-- `r15 = CF`. -/
def carryOut : List Instr := [.mov32 .r15 (.imm 0), .alu .adc .r15 (.imm 0)]

/-- `r8–r14 += r15 + 2²²⁴ r15` (`r15 < 2³²`, so `ror` by 32 shifts it left),
the carry out in `CF`. -/
def fold : List Instr :=
  [.mov .rax (.reg .r15), .shift .ror .rax 32] ++
    chain .add .adc W [.reg .r15, .imm 0, .imm 0, .reg .rax, .imm 0, .imm 0, .imm 0]

/-- `r8–r14 -= r15 + 2²²⁴ r15`, the borrow out in `CF`. -/
def unfold : List Instr :=
  [.mov .rax (.reg .r15), .shift .ror .rax 32] ++
    chain .sub .sbb W [.reg .r15, .imm 0, .imm 0, .reg .rax, .imm 0, .imm 0, .imm 0]

/-- `r8–r14 + 2⁴⁴⁸ r15`, for `r15 < 2³²`, folded into seven words: a second
fold never carries. -/
def fold2 : List Instr := fold ++ carryOut ++ fold

/-! ## Field arithmetic -/

/-- A product's term: `x · y` (twice if `dbl`), added to the accumulator
`r0 + 2⁶⁴ r1 + 2¹²⁸ r2`. -/
def term (x : Src) (y : Reg) (r0 r1 r2 : Reg) (dbl : Bool) : List Instr :=
  [.mov .rax x, .mul y] ++
    (if dbl then [.alu .add r0 (.reg .rax), .alu .adc r1 (.reg .rdx), .alu .adc r2 (.imm 0)]
      else []) ++
    [.alu .add r0 (.reg .rax), .alu .adc r1 (.reg .rdx), .alu .adc r2 (.imm 0)]

/-- A term of a product: `x_i · y_j`, twice if `dbl`. -/
structure Term where
  i : Nat
  j : Nat
  dbl : Bool
  deriving DecidableEq, Repr

/-- The accumulator's registers in column `k`: they rotate, the low word
of one column becoming the high word of the next once stored. -/
def accR (k : Nat) : Nat → Reg := fun n => [Reg.r15, .rcx, .rbp].getD ((k + n) % 3) .r15

/-- Column `k` of a product: its terms, then its low word stored at
`ACC + 8k` and cleared. -/
def column (x : Nat → Src) (y : Nat → Reg) (ts : List Term) (k : Nat) : List Instr :=
  ts.flatMap (fun t => term (x t.i) (y t.j) (accR k 0) (accR k 1) (accR k 2) t.dbl) ++
    [.store (sc (ACC + 8 * k)) (accR k 0), .mov32 (accR k 0) (.imm 0)]

/-- The fourteen columns of a product. -/
def columns (x : Nat → Src) (y : Nat → Reg) (cols : Nat → List Term) : List Instr :=
  (List.range 14).flatMap fun k => column x y (cols k) k

/-- The terms of column `k` of `a · b`. -/
def mulCol (k : Nat) : List Term :=
  ((List.range 7).filter fun i => k - i < 7 ∧ i ≤ k).map fun i => ⟨i, k - i, false⟩

/-- The terms of column `k` of `a²`: the cross products once, doubled, and
the square. -/
def sqrCol (k : Nat) : List Term :=
  ((List.range 7).filter fun i => k - i < 7 ∧ i < k - i).map (fun i => ⟨i, k - i, true⟩) ++
    if k % 2 = 0 ∧ k < 14 then [⟨k / 2, k / 2, false⟩] else []

/-- The accumulator's registers cleared. -/
def zeroAcc : List Instr := [.mov32 .r15 (.imm 0), .mov32 .rcx (.imm 0), .mov32 .rbp (.imm 0)]

/-- `t:c = t + c + ai · src` (a multiply-accumulate step; it never
overflows). `mov32` loads the low half of a word. -/
def mulStep (t c ai : Reg) (ld : Instr) : List Instr :=
  [ld, .mul ai, .alu .add .rax (.reg c), .alu .adc .rdx (.imm 0),
    .alu .add t (.reg .rax), .alu .adc .rdx (.imm 0), .mov c (.reg .rdx)]

/-- Multiply-accumulate steps along the registers `ts`, by `rcx`, the carry
in `rbp`: `ts + rbp = ts + rbp + rcx · vs`, where `lds` load the words `vs`. -/
def mulSteps : List Reg → List Instr → List Instr
  | t :: ts, ld :: lds => mulStep t .rbp .rcx ld ++ mulSteps ts lds
  | _, _ => []

/-- Word `i` of the product. -/
def h (i : Nat) : Nat := ACC + 8 * i

/-- The fourteen words of the product at `ACC`, reduced into `[o]`:
`L + H`, `+ (H - H mod 2²²⁴)`, `+ rot(H)`, then `fold2`. `rot(H)`, `H`
rotated by 224 bits, is `H`'s words loaded 4 bytes late: word `k` is the
word at `h (10 + k) + 4`, which holds the high half of `h (10 + k)` and the
low half of the next, but for word 3, whose halves (`h 13`'s high half and
`h 7`'s low half) are not next to each other in memory, and so are put
together in `rcx`. -/
def reduce (o : Nat) : List Instr :=
  [.mov32 .r15 (.imm 0)] ++ loads ACC W ++
  chain .add .adc W ((List.range 7).map fun i => .mem (sc (h (7 + i)))) ++
  [.alu .adc .r15 (.imm 0),
    .mov .rax (.mem (sc (h 10))), .mov32 .rdx (.reg .rax), .alu .sub .rax (.reg .rdx)] ++
  chain .add .adc [.r11, .r12, .r13, .r14, .r15]
    [.reg .rax, .mem (sc (h 11)), .mem (sc (h 12)), .mem (sc (h 13)), .imm 0] ++
  [.mov .rcx (.mem (sc (h 6 + 4))), .mov32 .rdx (.reg .rcx), .alu .sub .rcx (.reg .rdx),
    .mov32 .rdx (.mem (sc (h 13 + 4))), .alu .add .rcx (.reg .rdx)] ++
  chain .add .adc W [.mem (sc (h 10 + 4)), .mem (sc (h 11 + 4)), .mem (sc (h 12 + 4)), .reg .rcx,
    .mem (sc (h 7 + 4)), .mem (sc (h 8 + 4)), .mem (sc (h 9 + 4))] ++
  [.alu .adc .r15 (.imm 0)] ++ fold2 ++ stores o W

/-- `[o] = [a] · [b]` (`o` may be `a` or `b`). -/
def mul (o a b : Nat) : List Instr :=
  loads b W ++ zeroAcc ++
    columns (fun i => .mem (sc (a + 8 * i))) w mulCol ++ reduce o

/-- `[o] = [a]²` (`o` may be `a`). -/
def sqr (o a : Nat) : List Instr :=
  loads a W ++ zeroAcc ++ columns (fun i => .reg (w i)) w sqrCol ++ reduce o

/-- `[o] = k · [a]`, for a constant `k < 2³¹`. -/
def mulSmall (o a : Nat) (k : BitVec 32) : List Instr :=
  [.mov32 .rcx (.imm k), .mov32 .rbp (.imm 0)] ++
    (W.map fun r => .mov32 r (.imm 0)) ++
    mulSteps W ((List.range 7).map fun i => .mov .rax (.mem (sc (a + 8 * i)))) ++
    [.mov .r15 (.reg .rbp)] ++ fold2 ++ stores o W

/-- `[o] = [a] + [b]`. -/
def add (o a b : Nat) : List Instr :=
  loads a W ++ chain .add .adc W (words b) ++ carryOut ++ fold2 ++ stores o W

/-- `[o] = [a] - [b]`: a borrow out is `2⁴⁴⁸ ≡ 1 + 2²²⁴` too many, taken
out (twice at most). -/
def sub (o a b : Nat) : List Instr :=
  loads a W ++ chain .sub .sbb W (words b) ++ carryOut ++ unfold ++ carryOut ++ unfold ++
    stores o W

/-- Swaps `[x]` and `[y]` if the mask `rcx` is all ones (and not if it is
zero), word by word: `d = rcx ∧ (x ⊕ y)`, `x ⊕= d`, `y ⊕= d`. -/
def cswap (x y : Nat) : List Instr :=
  (List.range 7).flatMap fun i =>
    [.mov .rax (.mem (sc (x + 8 * i))), .mov .rdx (.mem (sc (y + 8 * i))),
      .mov .r8 (.reg .rax), .alu .xor .r8 (.reg .rdx), .alu .and .r8 (.reg .rcx),
      .alu .xor .rax (.reg .r8), .alu .xor .rdx (.reg .r8),
      .store (sc (x + 8 * i)) .rax, .store (sc (y + 8 * i)) .rdx]

/-- The ladder's `a24 = 39081`. -/
def a24 : BitVec 32 := 39081

/-- The field multiplications, as each implementation of X448 does them;
the rest of the code is the same for all. Each reads the working space and
writes `[o]` (which may be an operand) and the product's words `ACC`, and
uses only the registers `rax`, `rcx`, `rdx`, `rbp` and `r8–r15`. -/
structure Field where
  /-- `[o] = [a] · [b]` -/
  mul : Nat → Nat → Nat → List Instr
  /-- `[o] = [a]²` -/
  sqr : Nat → Nat → List Instr
  /-- `[o] = a24 · [a]` -/
  a24 : Nat → Nat → List Instr

/-- The baseline's: `mul`, `sqr` and `mulSmall`. -/
def baseline : Field where
  mul := mul
  sqr := sqr
  a24 o a := mulSmall o a a24

/-- `[o] = [a]^(2^n)`, for `n ≥ 1`: a square, then `n - 1` in place. -/
def sqn (F : Field) (o a n : Nat) : Prog isa :=
  if n = 1 then .block (F.sqr o a) else
  .seq (.block (F.sqr o a ++ [.mov32 .rbx (.imm (BitVec.ofNat 32 (n - 1)))]))
    (.loop (.block (F.sqr o o ++ [.alu .sub .rbx (.imm 1)])) .ne)

/-! ## The ladder -/

/-- One iteration of the ladder, for the bit `t = rbx - 1`: `k_t` from
`BITS`, `swap ^= k_t` into the mask `rcx = -swap`, the swaps, `swap = k_t`,
and the formulas of RFC 7748 §5, ordered by their dependencies rather than
as the RFC lists them, so that independent multiplications are next to each
other and the processor overlaps them. -/
def step (F : Field) : List Instr :=
  [.alu .sub .rbx (.imm 1), .movzx8 .rax { base := .rdi, index := some .rbx, disp := BITS },
    .mov .rdx (.mem (sc SWAP)), .alu .xor .rdx (.reg .rax), .store (sc SWAP) .rax,
    .mov32 .rcx (.imm 0), .alu .sub .rcx (.reg .rdx)] ++
  cswap X2 X3 ++ cswap Z2 Z3 ++
  add A X2 Z2 ++ sub B X2 Z2 ++ add C X3 Z3 ++ sub D X3 Z3 ++
  F.sqr AA A ++ F.sqr BB B ++ F.mul DA D A ++ F.mul CB C B ++
  sub E AA BB ++ sub Z3 DA CB ++ add X3 DA CB ++ F.a24 Z2 E ++
  F.sqr Z3 Z3 ++ F.sqr X3 X3 ++ add Z2 AA Z2 ++ F.mul Z3 X1 Z3 ++
  F.mul X2 AA BB ++ F.mul Z2 E Z2 ++
  [.alu .test .rbx (.reg .rbx)]

/-- The 448 iterations, for `t` from 447 down to 0. -/
def ladder (F : Field) : Prog isa :=
  .seq (.block [.mov32 .rbx (.imm 448)]) (.loop (.block (step F)) .ne)

/-- `[rdi + 8 rbx + BITS + j]`: bit `j` of byte `rbx` of the scalar. -/
def bitAt (j : Nat) : MemOp :=
  { base := .rdi, index := some .rbx, scale := 8, disp := ((BITS + j : Nat) : Int) }

/-- `BITS[8i + j] = bit j of scalar[i]`, for the 56 bytes `i` (the counter
`rbx`) of the scalar at `rsi`; then the clamped bits: `BITS[0..1] = 0` and
`BITS[447] = 1` (RFC 7748 §5, `decodeScalar448`). -/
def bits : Prog isa :=
  .seq (.block [.mov32 .rbx (.imm 0)]) (.seq (.loop (.block (
    [.movzx8 .rax { base := .rsi, index := some .rbx }] ++
    ((List.range 8).flatMap fun j =>
      [.mov .rdx (.reg .rax)] ++ (if j = 0 then [] else [.shift .shr .rdx j]) ++
      [.alu .and .rdx (.imm 1),
        .store8 (bitAt j) .rdx]) ++
    [.alu .add .rbx (.imm 1), .alu .cmp .rbx (.imm 56)])) .ne)
    (.block [.mov32 .rax (.imm 0), .store8 (sc BITS) .rax, .store8 (sc (BITS + 1)) .rax,
      .mov32 .rax (.imm 1), .store8 (sc (BITS + 447)) .rax]))

/-! ## Inversion

`[T7] = [Z2]^(p-2)`, by the addition chain `invert` of
`Proof/X448/Invert.lean`. -/

def invert (F : Field) : Prog isa :=
  .seq (sqn F T0 Z2 1) <| .seq (.block (F.mul T0 T0 Z2)) <|        -- z^(2^2 - 1)
  .seq (sqn F T1 T0 2) <| .seq (.block (F.mul T1 T1 T0)) <|        -- z^(2^4 - 1)
  .seq (sqn F T2 T1 4) <| .seq (.block (F.mul T2 T2 T1)) <|        -- z^(2^8 - 1)
  .seq (sqn F T3 T2 8) <| .seq (.block (F.mul T3 T3 T2)) <|        -- z^(2^16 - 1)
  .seq (sqn F T4 T3 16) <| .seq (.block (F.mul T4 T4 T3)) <|       -- z^(2^32 - 1)
  .seq (sqn F T5 T4 32) <| .seq (.block (F.mul T5 T5 T4)) <|       -- z^(2^64 - 1)
  .seq (sqn F T6 T5 64) <| .seq (.block (F.mul T6 T6 T5)) <|       -- z^(2^128 - 1)
  .seq (sqn F T6 T6 64) <| .seq (.block (F.mul T6 T6 T5)) <|       -- z^(2^192 - 1)
  .seq (sqn F T6 T6 16) <| .seq (.block (F.mul T6 T6 T3)) <|       -- z^(2^208 - 1)
  .seq (sqn F T6 T6 8) <| .seq (.block (F.mul T6 T6 T2)) <|        -- z^(2^216 - 1)
  .seq (sqn F T6 T6 4) <| .seq (.block (F.mul T6 T6 T1)) <|        -- z^(2^220 - 1)
  .seq (sqn F T6 T6 2) <| .seq (.block (F.mul T6 T6 T0)) <|        -- z^(2^222 - 1)
  .seq (sqn F T7 T6 1) <| .seq (.block (F.mul T7 T7 Z2)) <|        -- z^(2^223 - 1)
  .seq (sqn F T7 T7 225) <| .seq (sqn F T6 T6 2) <|
    .block (F.mul T6 T6 Z2 ++ F.mul T7 T7 T6)                     -- z^(p - 2)

/-! ## Encoding and decoding -/

/-- The fully reduced `[a]` (`< p`) into `r8–r14`: `y = x + 1 + 2²²⁴`,
whose carry out is set exactly when `x ≥ p`, and then `y mod 2⁴⁴⁸ = x - p`
is selected with the mask `r15 = -carry`. -/
def freeze (a : Nat) : List Instr :=
  [.mov32 .r15 (.imm 1)] ++ loads a W ++ fold ++ [.alu .sbb .r15 (.reg .r15)] ++
  (List.range 7).flatMap fun i =>
    [.mov .rax (.mem (sc (a + 8 * i))), .alu .xor (w i) (.reg .rax), .alu .and (w i) (.reg .r15),
      .alu .xor (w i) (.reg .rax)]

/-- The callee-saved registers we use, and where they are saved. -/
def saved : List (Reg × Nat) :=
  [(.rbx, 0), (.rbp, 8), (.r12, 16), (.r13, 24), (.r14, 32), (.r15, 40)]

/-- Saves them (with the working space in `rcx`). -/
def save : List Instr := saved.map fun (r, d) => .store (at_ .rcx d) r

def restore : List Instr := saved.map fun (r, d) => .mov r (.mem (sc d))

/-- Reads the arguments (with the working space in `rcx`): the
`out` into `r15`, the working space into `rdi`, the u-coordinate's seven
words (all 448 bits are used) into `X1` and `X3`, and `x2 = 1`, `z2 = 0`,
`z3 = 1`, `swap = 0`. The scalar stays at `rsi` for `bits`. -/
def setup : List Instr :=
  save ++ [.mov .r15 (.reg .rdi), .mov .rdi (.reg .rcx)] ++
    (List.range 7).map (fun i => .mov (w i) (.mem (at_ .rdx (8 * i)))) ++
    stores X1 W ++ stores X3 W ++
    [.mov32 .rax (.imm 0), .mov32 .rdx (.imm 1)] ++
    stores X2 [.rdx, .rax, .rax, .rax, .rax, .rax, .rax] ++
    stores Z2 [.rax, .rax, .rax, .rax, .rax, .rax, .rax] ++
    stores Z3 [.rdx, .rax, .rax, .rax, .rax, .rax, .rax] ++ [.store (sc SWAP) .rax]

/-- `x2 · z2^(p-2)`, reduced fully, to `out`, and then the saved registers
restored (the stores do not touch the working space). -/
def finish (F : Field) : List Instr :=
  F.mul X2 X2 T7 ++ freeze X2 ++
    (List.range 7).map (fun i => .store (at_ .rsi (8 * i)) (w i)) ++ restore

/-- The swap after the loop. -/
def lastSwap : List Instr :=
  [.mov .rdx (.mem (sc SWAP)), .mov32 .rcx (.imm 0), .alu .sub .rcx (.reg .rdx)] ++
  cswap X2 X3 ++ cswap Z2 Z3

/-- X448 with the ladder `lad` (which leaves the ladder's final state in the
working space as `ladder` does) and the field multiplications `F` for the
inversion. -/
def x448Of (F : Field) (lad : Prog isa) : Prog isa :=
  .seq (.block setup) <| .seq bits <| .seq (.block [.mov .rsi (.reg .r15)]) <| .seq lad <|
    .seq (.block lastSwap) <| .seq (invert F) (.block (finish F))

/-- X448 with the field multiplications `F`. -/
def x448With (F : Field) : Prog isa := x448Of F (ladder F)

def x448 : Prog isa := x448With baseline

end VG.Impl.X448.X86_64
