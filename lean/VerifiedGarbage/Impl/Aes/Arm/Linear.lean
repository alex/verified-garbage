import VerifiedGarbage.Impl.Aes.Arm.Sbox

/-!
# The linear layers of bitsliced AES on ARMv7

The state of two blocks is eight 32-bit words in `q 0 … q 7`, word `j`
holding bit `j` of the 32 bytes: byte `i = r + 4c` (row `r`, column `c`)
of block `b` is at bit position `8r + 2c + b`, as in BearSSL's `aes_ct`
(Thomas Pornin, MIT licence), whose `ortho`, `shift_rows` and
`mix_columns` these follow. So ShiftRows rotates each 8-bit row, and
MixColumns rotates whole words by 8 and 16 bits.

The model has no `lsl` in the abstract evaluation the proofs use, so a
left shift by `s` of a value whose top `s` bits are zero (after masking)
is written as a rotation right by `32 - s`, which is the same.

Every block here uses the state registers and the temporaries `t0`, `t1`
and `u7`; the transposes build their masks in `t1` (with `movw` and
`movt`), and AddRoundKey loads the round key from `kp`. None uses memory
otherwise.
-/

namespace VG.Impl.Aes.Arm

open VG.Arm

/-- The temporaries. -/
def t0 : Reg := .r10
def t1 : Reg := .r11
def u7 : Reg := .r12

/-- The register pointing to the round key. -/
def kp : Reg := .r9

def rorOp (r : Reg) (n : Nat) : Op2 := .shifted r .ror n
def lsrOp (r : Reg) (n : Nat) : Op2 := .shifted r .lsr n

/-- `d := v`, with `movw` and `movt`. -/
def imm32 (d : Reg) (v : BitVec 32) : List Instr :=
  [.movw d (v.extractLsb' 0 16), .movt d (v.extractLsb' 16 16)]

/-! ## Between words of the blocks and the bitsliced state -/

/-- A delta swap between `x` and `y` (BearSSL's `SWAPN`): exchanges the bits
of `y` in the mask (in `t1`) with the bits of `x` `s` places above them. -/
def swapBetween (x y : Reg) (s : Nat) : List Instr :=
  [.dp .eor t0 y (lsrOp x s), .dp .and t0 t0 (.reg t1), eorR y y t0, .dp .eor x x (rorOp t0 (32 - s))]

/-- BearSSL's `br_aes_ct_ortho`: transposes the 8×8 bit matrix in each
byte position of the eight words. Its own inverse: it takes word `k` of
block `b` (bytes `4k … 4k + 3`, little-endian) in `q (2k + b)` to the
bitsliced state, and back. -/
def ortho : List Instr :=
  imm32 t1 0x55555555 ++
  ([(0, 1), (2, 3), (4, 5), (6, 7)].flatMap fun (a, b) => swapBetween (q a) (q b) 1) ++
  imm32 t1 0x33333333 ++
  ([(0, 2), (1, 3), (4, 6), (5, 7)].flatMap fun (a, b) => swapBetween (q a) (q b) 2) ++
  imm32 t1 0x0F0F0F0F ++
  ([(0, 4), (1, 5), (2, 6), (3, 7)].flatMap fun (a, b) => swapBetween (q a) (q b) 4)

/-! ## The round transformations -/

/-- ShiftRows of one word (BearSSL's `shift_rows`): row `r` (bits `8r …
8r + 7`) rotates right by `2r` bits within its byte, keeping the part of
each row that moves down and the part that wraps around separately. -/
def srWord (x : Reg) : List Instr :=
  [.dp .and t0 x (.imm 0x000000FF),
   .dp .and t1 x (.imm 0x0000FC00), .dp .eor t0 t0 (rorOp t1 2),
   .dp .and t1 x (.imm 0x00000300), .dp .eor t0 t0 (rorOp t1 26),
   .dp .and t1 x (.imm 0x00F00000), .dp .eor t0 t0 (rorOp t1 4),
   .dp .and t1 x (.imm 0x000F0000), .dp .eor t0 t0 (rorOp t1 28),
   .dp .and t1 x (.imm 0xC0000000), .dp .eor t0 t0 (rorOp t1 6),
   .dp .and t1 x (.imm 0x3F000000), .dp .eor t0 t0 (rorOp t1 30),
   movR x t0]

def shiftRows : List Instr := (List.range 8).flatMap fun j => srWord (q j)

/-- The register that output word `j` of MixColumns is computed in. -/
def mcOut (j : Nat) : Reg := if j = 0 then t0 else if j = 1 then t1 else q (j - 2)

/-- Output word `j` of MixColumns (BearSSL's `mix_columns`): with
`rⱼ = qⱼ ⋙ 8` (the next row) and `uⱼ = qⱼ ⊕ rⱼ`, it is
`uⱼ₋₁ ⊕ [j ∈ {0, 1, 3, 4}] u₇ ⊕ rⱼ ⊕ (uⱼ ⋙ 16)` (the multiplication by
`{02}` of `uⱼ` moves bit `j - 1` to `j` and reduces by `{1b}`). `q (j - 1)`
holds `uⱼ₋₁`, and `q j` is left holding `uⱼ`. -/
def mcWord (j : Nat) : List Instr :=
  [.mov (mcOut j) (rorOp (q j) 8), eorR (q j) (q j) (mcOut j)] ++
  (if j = 0 then [] else [eorR (mcOut j) (mcOut j) (q (j - 1))]) ++
  (if j = 0 ∨ j = 1 ∨ j = 3 ∨ j = 4 then [eorR (mcOut j) (mcOut j) u7] else []) ++
  [.dp .eor (mcOut j) (mcOut j) (rorOp (q j) 16)]

def mixColumns : List Instr :=
  [.dp .eor u7 (q 7) (rorOp (q 7) 8)] ++
  (List.range 8).flatMap mcWord ++
  ((List.range 8).reverse.map fun j => movR (q j) (mcOut j))

/-- AddRoundKey, with the bitsliced round key at `kp`. -/
def addRoundKey : List Instr :=
  (List.range 8).flatMap fun j => [.ldr t0 kp (4 * j), eorR (q j) (q j) t0]

end VG.Impl.Aes.Arm
