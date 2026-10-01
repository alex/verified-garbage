import VerifiedGarbage.TCB.X86_64.Isa

/-!
# X448: x86-64 implementation

`vg_x448(out = rdi, scalar = rsi, point = rdx, scratch = rcx)`.

A field element is sixteen 28-bit limbs, each stored in a 64-bit word.
The limbs are normalized after every operation. Multiplication accumulates
sixteen rows into 32 words; every coefficient fits in 64 bits. Reduction
uses `2^448 = 2^224 + 1` modulo the field prime, then propagates carries.

The working space stays in `rdi`, and the output pointer in `rsi` after
scalar decoding. `rbx` counts ladder iterations and runs of squarings. Multiplication
uses its own row counter `r10` and pointer `r11`. The only callee-saved
registers used are `rbx` and `r12`, saved in the working space.

The ladder follows RFC 7748 §5, with an addition chain for inversion.
All branches and addresses depend only on pointers and loop counters.
-/

namespace VG.Impl.X448.X86_64

open VG.X86_64

def at_ (b : Reg) (d : Nat) : MemOp := { base := b, disp := d }
def sc (d : Nat) : MemOp := at_ .rdi d

/-- Each field element occupies 128 bytes. -/
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
def T0 : Nat := slot 14
def T1 : Nat := slot 15
def T2 : Nat := slot 16
def T3 : Nat := slot 17
def T4 : Nat := slot 18
def T5 : Nat := slot 19
def T6 : Nat := slot 20
def T7 : Nat := slot 21
def SWAP : Nat := 16
def BITS : Nat := 3072
def ACC : Nat := 3584
def TMP : Nat := 3840

/-- The low 28 bits. -/
def mask28 : BitVec 32 := 0x0fffffff

/-- Copy the sixteen limbs. -/
def copy (o a : Nat) : List Instr :=
  (List.range 16).flatMap fun i =>
    [.mov .rax (.mem (sc (a + 8 * i))), .store (sc (o + 8 * i)) .rax]

/-- One carry step from `a` to `o`, with the incoming carry in `rcx`. -/
def carryStep (o a i : Nat) : List Instr :=
  [.mov .rax (.mem (sc (a + 8 * i))), .alu .add .rcx (.reg .rax), .mov .rax (.reg .rcx),
    .alu .and .rax (.imm mask28), .store (sc (o + 8 * i)) .rax, .shift .shr .rcx 28]

/-- Normalize the limbs, returning the carry out in `rcx`. -/
def pass (o a : Nat) : List Instr :=
  .mov32 .rcx (.imm 0) :: (List.range 16).flatMap (carryStep o a)

/-- Fold the carry out of limb 15 into limbs 0 and 8 of `TMP`. -/
def fold : List Instr :=
  [0, 8].flatMap fun i =>
    [.mov .rax (.mem (sc (TMP + 8 * i))), .alu .add .rax (.reg .rcx),
      .store (sc (TMP + 8 * i)) .rax]

/-- Three passes suffice for coefficients below `2^62`. The first two
carry-outs are folded at bit positions 0 and 224; the third is zero. -/
def normalize (o : Nat) : List Instr :=
  pass TMP TMP ++ fold ++ pass TMP TMP ++ fold ++ pass o TMP

/-- Add one product to a coefficient of the current row. `rcx` holds
`a_i`; `r11` is the working-space pointer plus `8*i`. -/
def rowStep (b j : Nat) : List Instr :=
  [.mov .rax (.mem (sc (b + 8 * j))), .mul .rcx,
    .alu .add .rax (.mem (at_ .r11 (ACC + 8 * j))),
    .store (at_ .r11 (ACC + 8 * j)) .rax]

def row (a b : Nat) : List Instr :=
  [.mov .rcx (.mem { base := .rdi, index := some .r10, scale := 8, disp := a })] ++
  (List.range 16).flatMap (rowStep b) ++
  [.alu .add .r11 (.imm 8), .alu .add .r10 (.imm 1), .alu .cmp .r10 (.imm 16)]

/-- Product coefficients at indices `k`, `k+16`, and those which fold
twice because their degree is at least 24. -/
def reduceCol (k : Nat) : List Instr :=
  [.mov .rax (.mem (sc (ACC + 8 * k))),
    .alu .add .rax (.mem (sc (ACC + 8 * (k + 16))))] ++
  (if k < 8 then [.alu .add .rax (.mem (sc (ACC + 8 * (k + 24))))]
   else [.alu .add .rax (.mem (sc (ACC + 8 * (k + 8)))),
     .alu .add .rax (.mem (sc (ACC + 8 * (k + 16))))]) ++
  [.store (sc (TMP + 8 * k)) .rax]

/-- `[o] = [a] * [b]`; either input may also be the output. -/
def mul (o a b : Nat) : Prog isa :=
  .seq (.block ([.mov32 .rax (.imm 0)] ++
    (List.range 32).map (fun i => .store (sc (ACC + 8 * i)) .rax) ++
    [.mov32 .r10 (.imm 0), .mov .r11 (.reg .rdi)])) <|
  .seq (.loop (.block (row a b)) .ne) <|
    .block ((List.range 16).flatMap reduceCol ++ normalize o)

/-- Limb `i` of `2p`, allowing subtraction without a negative limb. -/
def subK (i : Nat) : BitVec 32 := if i = 8 then 0x1ffffffc else 0x1ffffffe

def add (o a b : Nat) : List Instr :=
  (List.range 16).flatMap (fun i =>
    [.mov .rax (.mem (sc (a + 8 * i))), .alu .add .rax (.mem (sc (b + 8 * i))),
      .store (sc (TMP + 8 * i)) .rax]) ++ normalize o

def sub (o a b : Nat) : List Instr :=
  (List.range 16).flatMap (fun i =>
    [.mov .rax (.mem (sc (a + 8 * i))), .alu .add .rax (.imm (subK i)),
      .alu .sub .rax (.mem (sc (b + 8 * i))), .store (sc (TMP + 8 * i)) .rax]) ++ normalize o

def mulSmall (o a : Nat) : List Instr :=
  [.mov32 .rcx (.imm 39081)] ++ (List.range 16).flatMap (fun i =>
    [.mov .rax (.mem (sc (a + 8 * i))), .mul .rcx, .store (sc (TMP + 8 * i)) .rax]) ++ normalize o

/-- Swap the two slots under the mask in `rcx`. -/
def cswap (x y : Nat) : List Instr :=
  (List.range 16).flatMap fun i =>
    [.mov .rax (.mem (sc (x + 8 * i))), .mov .rdx (.mem (sc (y + 8 * i))),
      .mov .r8 (.reg .rax), .alu .xor .r8 (.reg .rdx), .alu .and .r8 (.reg .rcx),
      .alu .xor .rax (.reg .r8), .alu .xor .rdx (.reg .r8),
      .store (sc (x + 8 * i)) .rax, .store (sc (y + 8 * i)) .rdx]

inductive Op
  | mul (o a b : Nat)
  | mulSmall (o a : Nat)
  | add (o a b : Nat)
  | sub (o a b : Nat)
  | copy (o a : Nat)
  deriving DecidableEq, Repr

def Op.code : Op → Prog isa
  | .mul o a b => X86_64.mul o a b
  | .mulSmall o a => .block (X86_64.mulSmall o a)
  | .add o a b => .block (X86_64.add o a b)
  | .sub o a b => .block (X86_64.sub o a b)
  | .copy o a => .block (X86_64.copy o a)

def ops : List Op → Prog isa
  | [] => .block []
  | o :: os => .seq o.code (ops os)

def stepOps : List Op :=
  [.add A X2 Z2, .mul AA A A, .sub B X2 Z2, .mul BB B B, .sub E AA BB,
    .add C X3 Z3, .sub D X3 Z3, .mul DA D A, .mul CB C B,
    .add X3 DA CB, .mul X3 X3 X3, .sub Z3 DA CB, .mul Z3 Z3 Z3, .mul Z3 X1 Z3,
    .mul X2 AA BB, .mulSmall Z2 E, .add Z2 AA Z2, .mul Z2 E Z2]

def stepHead : List Instr :=
  [.alu .sub .rbx (.imm 1), .movzx8 .rax { base := .rdi, index := some .rbx, disp := BITS },
    .mov .rdx (.mem (sc SWAP)), .alu .xor .rdx (.reg .rax), .store (sc SWAP) .rax,
    .mov32 .rcx (.imm 0), .alu .sub .rcx (.reg .rdx)] ++ cswap X2 X3 ++ cswap Z2 Z3

def step : Prog isa :=
  .seq (.block stepHead) (.seq (ops stepOps) (.block [.alu .test .rbx (.reg .rbx)]))

def ladder : Prog isa := .seq (.block [.mov32 .rbx (.imm 448)]) (.loop step .ne)

def lastSwap : List Instr :=
  [.mov .rdx (.mem (sc SWAP)), .mov32 .rcx (.imm 0), .alu .sub .rcx (.reg .rdx)] ++
  cswap X2 X3 ++ cswap Z2 Z3

/-- Square `n` times in place, for `n > 0`. -/
def sqn (o n : Nat) : Prog isa :=
  .seq (.block [.mov32 .rbx (.imm (BitVec.ofNat 32 n))])
    (.loop (.seq (mul o o o) (.block [.alu .sub .rbx (.imm 1)])) .ne)

def invert : Prog isa :=
  .seq (ops [.copy T0 Z2]) <| .seq (sqn T0 1) <| .seq (ops [.mul T0 T0 Z2, .copy T1 T0]) <|
  .seq (sqn T1 2) <| .seq (ops [.mul T1 T1 T0, .copy T2 T1]) <|
  .seq (sqn T2 4) <| .seq (ops [.mul T2 T2 T1, .copy T3 T2]) <|
  .seq (sqn T3 8) <| .seq (ops [.mul T3 T3 T2, .copy T4 T3]) <|
  .seq (sqn T4 16) <| .seq (ops [.mul T4 T4 T3, .copy T5 T4]) <|
  .seq (sqn T5 32) <| .seq (ops [.mul T5 T5 T4, .copy T6 T5]) <|
  .seq (sqn T6 64) <| .seq (ops [.mul T6 T6 T5]) <|
  .seq (sqn T6 64) <| .seq (ops [.mul T6 T6 T5]) <|
  .seq (sqn T6 16) <| .seq (ops [.mul T6 T6 T3]) <|
  .seq (sqn T6 8) <| .seq (ops [.mul T6 T6 T2]) <|
  .seq (sqn T6 4) <| .seq (ops [.mul T6 T6 T1]) <|
  .seq (sqn T6 2) <| .seq (ops [.mul T6 T6 T0, .copy T7 T6]) <|
  .seq (sqn T7 1) <| .seq (ops [.mul T7 T7 Z2]) <|
  .seq (sqn T7 225) <| .seq (sqn T6 2) <| ops [.mul T6 T6 Z2, .mul T7 T7 T6]

/-- Decode seven bytes into two limbs, without reading past the input. -/
def decodePair (i : Nat) : List Instr :=
  [.mov32 .r9 (.imm 256), .mov32 .rax (.imm 0)] ++ (List.range 7).flatMap (fun j =>
    [.mul .r9, .movzx8 .r8 (at_ .r10 (7 * i + (6 - j))), .alu .add .rax (.reg .r8)]) ++
  [.mov .r8 (.reg .rax), .alu .and .r8 (.imm mask28),
    .store (sc (X1 + 16 * i)) .r8, .store (sc (X3 + 16 * i)) .r8,
    .shift .shr .rax 28, .store (sc (X1 + 16 * i + 8)) .rax,
    .store (sc (X3 + 16 * i + 8)) .rax]

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

/-- Initialize every remaining slot with bounded limbs. `X1` and `X3`
already contain the decoded input. -/
def initSlots : List Instr :=
  [.mov32 .rax (.imm 0)] ++
  (List.range 32).map (fun i => .store (sc (X2 + 8 * i)) .rax) ++
  (List.range 288).map (fun i => .store (sc (Z3 + 8 * i)) .rax) ++
  [.store (sc SWAP) .rax, .mov32 .rax (.imm 1), .store (sc X2) .rax, .store (sc Z3) .rax]

def setup : List Instr :=
  [.store (at_ .rcx 0) .rbx, .store (at_ .rcx 8) .r12,
    .mov .r12 (.reg .rdi), .mov .rdi (.reg .rcx), .mov .r10 (.reg .rdx)] ++
  (List.range 8).flatMap decodePair ++ initSlots

/-- Add `1 + 2^224` and keep the carry: it is one exactly when `[X2] >= p`. -/
def freeze : List Instr :=
  copy TMP X2 ++ [0, 8].flatMap (fun i =>
    [.mov .rax (.mem (sc (TMP + 8 * i))), .alu .add .rax (.imm 1),
      .store (sc (TMP + 8 * i)) .rax]) ++ pass TMP TMP ++
  [.mov32 .r8 (.imm 0), .alu .sub .r8 (.reg .rcx)] ++
  (List.range 16).flatMap fun i =>
    [.mov .rax (.mem (sc (X2 + 8 * i))), .mov .rdx (.mem (sc (TMP + 8 * i))),
      .alu .xor .rdx (.reg .rax), .alu .and .rdx (.reg .r8), .alu .xor .rax (.reg .rdx),
      .store (sc (X2 + 8 * i)) .rax]

/-- Pack two limbs into seven output bytes. -/
def packPair (i : Nat) : List Instr :=
  [.mov32 .rcx (.imm 0x10000000), .mov .rax (.mem (sc (X2 + 16 * i + 8))),
    .mul .rcx, .alu .add .rax (.mem (sc (X2 + 16 * i)))] ++
  (List.range 7).flatMap fun j => [.store8 (at_ .rsi (7 * i + j)) .rax, .shift .shr .rax 8]

def finish : Prog isa :=
  .seq (mul X2 X2 T7) (.block (freeze ++ (List.range 8).flatMap packPair ++
    [.mov .rbx (.mem (sc 0)), .mov .r12 (.mem (sc 8))]))

def x448 : Prog isa :=
  .seq (.block setup) <| .seq bits <| .seq (.block [.mov .rsi (.reg .r12)]) <|
    .seq ladder <| .seq (.block lastSwap) <| .seq invert finish

end VG.Impl.X448.X86_64
