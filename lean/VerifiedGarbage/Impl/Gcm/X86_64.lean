import VerifiedGarbage.TCB.X86_64.Isa

/-!
# GHASH: x86-64 implementation

`vg_ghash(h = rdi, y = rsi, data = rdx, n = rcx, scratch = r8)`.

For each of the `n` blocks `X` at `data`, `Y := (Y ⊕ X) • H`, with the
carry-less products computed by integer multiplications with "holes", as in
BearSSL's `ghash_ctmul64.c` (Thomas Pornin, MIT licence; see
<https://www.bearssl.org/ctmul.html>):

* A block is big-endian: each 8-byte half is loaded with `mov` and `bswap`.
  The first half `A` holds the coefficients of `x⁰ … x⁶³` (the most
  significant bit is `x⁰`, SP 800-38D's bit order), the second `B` those of
  `x⁶⁴ … x¹²⁷`. In this bit-reflected order, the integer-style carry-less
  product of two 64-bit words `a, b` is the 128-bit word of `x · a · b`.
* The carry-less product of two words `a` and `b` (`product`): the bits of
  `b` are split into the four classes `b & cls j` (the bits `j mod 4`), and
  those of `a` into eight: the four classes, each in the low and the high 32
  bits (`half i h`). The integer product (`mul`) of a part of `a` in class
  `i` and a part of `b` in class `j` has in each bit position of class
  `i + j mod 4` the sum of at most 8 bit products, which is less than 16, so
  its carries never reach the next bit of that class: those bits are the
  bits of the carry-less product. The products of each class `k` are added
  (XOR) in `r12:r11`, masked with `cls k` and added to the result in
  `r14:r13`. (With 16 bits per part, a sum could reach 16 and carry into the
  next bit of the class; splitting `a` into halves also keeps the high half
  of each product, in `rdx`, exact, so that no bit reversal is needed.)
* `Y • H` is `x⁻¹ · (Y · H)`, so the code multiplies by `H' = x⁻¹ · H`
  instead, computed once: `H' = (H <<< 1) ⊕ (x⁻¹ if the bit shifted out is
  1)`, where `x⁻¹ = 1 + x + x⁶ + x¹²⁷`. The 24 parts of `H'_A`, `H'_B` and
  `H'_A ⊕ H'_B` are stored in `scratch[48..240)`.
* Each block takes three word products (Karatsuba): `A = Y_A · H'_A`,
  `B = Y_B · H'_B`, `M = (Y_A ⊕ Y_B) · (H'_A ⊕ H'_B)`, which give the 256-bit
  product `W₀ ‖ W₁ ‖ W₂ ‖ W₃` of `x · Y · H' = Y · H` (`W₀` the lowest
  powers).
* The reduction modulo `x¹²⁸ + x⁷ + x² + x + 1` folds `W₃` into `W₁, W₂`,
  then `W₂` into `W₀, W₁` (`fold`), using `x¹²⁸ = 1 + x + x² + x⁷`.
* `Y ⊕ X` and partial results are kept in `y` and in `scratch[240..256)`
  while registers are short. `Y` is written back to `y` after every block.
* `rbx, rbp, r12–r15` are saved in `scratch[0..48)` and restored on exit.
* `rdi, rsi, rdx, rcx, r8` (the pointers and the block count) are public;
  no address and no branch depends on anything else, and `mul` takes the
  same time for every operand.
-/

namespace VG.Impl.Gcm.X86_64

open VG.X86_64

def at_ (b : Reg) (d : Nat) : MemOp := { base := b, disp := d }

/-- The bits of class `i` (the bit positions `i mod 4`). -/
def cls (i : Nat) : BitVec 64 := 0x1111111111111111 <<< i

/-- The bits of class `i` in the low (`h = 0`) or high (`h = 1`) 32 bits. -/
def half (i h : Nat) : BitVec 64 := cls i &&& (0xFFFFFFFF <<< (32 * h))

/-- The classes of the second factor. -/
def B : Nat → Reg
  | 0 => .rbx
  | 1 => .rbp
  | 2 => .r9
  | _ => .r10

/-- The sum of the products of one class, and of the result. -/
def AL : Reg := .r11
def AH : Reg := .r12
def PL : Reg := .r13
def PH : Reg := .r14
/-- `Y_A`, then `W₀`. -/
def W0 : Reg := .r15

/-- Where in `scratch` part `u` of `H'` is: the table `u / 8` (`H'_A`,
`H'_B`, `H'_A ⊕ H'_B`), part `half (u % 8 / 2) (u % 2)`. -/
def off (u : Nat) : Nat := 48 + 8 * u

/-- Where `Y_A ⊕ Y_B` and `W₃` are kept. -/
def slotM : Nat := 240
def slotW : Nat := 248

/-- The `t`-th of the eight products of class `k`, with table `q`. -/
def term (q k t : Nat) : List Instr := [
  .mov .rax (.mem (at_ .r8 (off (8 * q + t)))),
  .mul (B ((k + 4 - t / 2) % 4)),
  .alu .xor AL (.reg .rax),
  .alu .xor AH (.reg .rdx)]

/-- The products of class `k`, masked and added to the result. -/
def clsCode (q k : Nat) : List Instr :=
  [.mov AL (.imm 0), .mov AH (.imm 0)] ++ (List.range 8).flatMap (term q k) ++
  [.movImm64 .rax (cls k), .alu .and AL (.reg .rax), .alu .and AH (.reg .rax),
   .alu .xor PL (.reg AL), .alu .xor PH (.reg AH)]

/-- The classes of the second factor `y`. -/
def split (y : Src) : List Instr :=
  (List.range 4).flatMap fun j => [.movImm64 (B j) (cls j), .alu .and (B j) y]

/-- `PH:PL` := the carry-less product of table `q`'s word and `y`. -/
def product (y : Src) (q : Nat) : List Instr :=
  split y ++ [.mov PL (.imm 0), .mov PH (.imm 0)] ++ (List.range 4).flatMap (clsCode q)

/-- `x¹²⁸ · w` added to `lo` and `hi` (the next 64 powers): `lo ⊕= w ⊕
(w >> 1) ⊕ (w >> 2) ⊕ (w >> 7)`, `hi ⊕= (w << 63) ⊕ (w << 62) ⊕ (w << 57)`. -/
def fold (w lo hi : Reg) : List Instr := [
  .alu .xor lo (.reg w),
  .mov .rax (.reg w), .shift .shr .rax 1, .alu .xor lo (.reg .rax),
  .mov .rax (.reg w), .shift .shr .rax 2, .alu .xor lo (.reg .rax),
  .mov .rax (.reg w), .shift .shr .rax 7, .alu .xor lo (.reg .rax),
  .mov .rax (.reg w), .alu .and .rax (.imm 1), .shift .ror .rax 1, .alu .xor hi (.reg .rax),
  .mov .rax (.reg w), .alu .and .rax (.imm 3), .shift .ror .rax 2, .alu .xor hi (.reg .rax),
  .mov .rax (.reg w), .alu .and .rax (.imm 0x7f), .shift .ror .rax 7, .alu .xor hi (.reg .rax)]

/-- Load `Y ⊕ X`: `Y_A` in `W0`, `Y_B` in `y[8..16)`, `Y_A ⊕ Y_B` in `scratch`. -/
def load : List Instr := [
  .mov W0 (.mem (at_ .rsi 0)), .bswap W0,
  .mov .rax (.mem (at_ .rdi 0)), .bswap .rax,
  .alu .xor W0 (.reg .rax),
  .mov AL (.mem (at_ .rsi 8)), .bswap AL,
  .mov .rax (.mem (at_ .rdi 8)), .bswap .rax,
  .alu .xor AL (.reg .rax),
  .store (at_ .rsi 8) AL,
  .alu .xor AL (.reg W0),
  .store (at_ .r8 slotM) AL]

/-- `W0 := A_hi`, `y[0..8) := A_lo`. -/
def keepA : List Instr := [.mov W0 (.reg PH), .store (at_ .rsi 0) PL]

/-- `y := (A_lo ⊕ B_hi ⊕ A_hi, A_lo ⊕ B_hi ⊕ B_lo)`, `W₃ = B_lo` to `scratch`. -/
def keepB : List Instr := [
  .mov .rax (.mem (at_ .rsi 0)),
  .alu .xor .rax (.reg PH),
  .mov AL (.reg .rax),
  .alu .xor AL (.reg W0),
  .alu .xor .rax (.reg PL),
  .store (at_ .rsi 0) AL,
  .store (at_ .rsi 8) .rax,
  .store (at_ .r8 slotW) PL]

/-- `W₁` in `AL`, `W₂` in `AH`, `W₃` in `PL`. -/
def keepM : List Instr := [
  .mov AL (.mem (at_ .rsi 0)), .alu .xor AL (.reg PH),
  .mov AH (.mem (at_ .rsi 8)), .alu .xor AH (.reg PL),
  .mov PL (.mem (at_ .r8 slotW))]

/-- Store the new `Y = W₀ ‖ W₁`, advance to the next block and decrement the
count (setting ZF when it hits 0). -/
def store : List Instr := [
  .bswap W0, .store (at_ .rsi 0) W0,
  .bswap AL, .store (at_ .rsi 8) AL,
  .alu .add .rdi (.imm 16), .alu .sub .rcx (.imm 1)]

/-- One block. -/
def body : List Instr :=
  load ++ product (.reg W0) 0 ++ keepA ++ product (.mem (at_ .rsi 8)) 1 ++ keepB ++
    product (.mem (at_ .r8 slotM)) 2 ++ keepM ++ fold PL AL AH ++ fold AH W0 AL ++ store

/-- The callee-saved registers we use, and where they are saved. -/
def saved : List (Reg × Nat) := [(.rbx, 0), (.rbp, 8), (.r12, 16), (.r13, 24), (.r14, 32), (.r15, 40)]

def save : List Instr := saved.map fun (r, d) => .store (at_ .r8 d) r
def restore : List Instr := saved.map fun (r, d) => .mov r (.mem (at_ .r8 d))

/-- The high word of `x⁻¹ = 1 + x + x⁶ + x¹²⁷` (its low word is 1). -/
def xInvHigh : BitVec 64 := 0xC200000000000000

/-- `H' = x⁻¹ · H`: `H'_A` in `AL`, `H'_B` in `AH`, `H'_A ⊕ H'_B` in `PH`. -/
def hInv : List Instr := [
  .mov AL (.mem (at_ .rdi 0)), .bswap AL,
  .mov AH (.mem (at_ .rdi 8)), .bswap AH,
  .alu .add AH (.reg AH), .alu .adc AL (.reg AL),
  .alu .sbb .rax (.reg .rax),
  .movImm64 PL xInvHigh, .alu .and PL (.reg .rax), .alu .xor AL (.reg PL),
  .alu .and .rax (.imm 1), .alu .xor AH (.reg .rax),
  .mov PH (.reg AL), .alu .xor PH (.reg AH)]

/-- The word of table `q`. -/
def tblReg : Nat → Reg
  | 0 => AL
  | 1 => AH
  | _ => PH

/-- Part `u` of the tables. -/
def entry (u : Nat) : List Instr := [
  .movImm64 .rax (half (u % 8 / 2) (u % 2)),
  .alu .and .rax (.reg (tblReg (u / 8))),
  .store (at_ .r8 (off u)) .rax]

/-- Save registers, compute the tables, move `data` to `rdi` (`mul` writes
`rdx`) and test `n`. -/
def setup : List Instr :=
  save ++ hInv ++ (List.range 24).flatMap entry ++ [.mov .rdi (.reg .rdx), .alu .test .rcx (.reg .rcx)]

def ghash : Prog isa :=
  .seq (.block setup)
    (.seq (.ite .e (.block []) (.loop (.block body) .ne)) (.block restore))

end VG.Impl.Gcm.X86_64
