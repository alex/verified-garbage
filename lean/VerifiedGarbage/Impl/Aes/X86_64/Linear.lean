import VerifiedGarbage.Impl.Aes.X86_64.Sbox

/-!
# The linear layers of bitsliced AES on x86-64

The state of four blocks is eight 64-bit words in `q 0 … q 7`, word `j`
holding bit `j` of the 64 bytes: byte `i = r + 4c` (row `r`, column `c`)
of block `b` is at bit position `16r + 4c + b`, as in BearSSL's
`aes_ct64` (Thomas Pornin, MIT licence), whose `ortho`, `interleave_in`,
`shift_rows` and `mix_columns` these follow. So ShiftRows rotates each
16-bit row, and MixColumns rotates whole words by 16 and 32 bits.

Every block here uses the state registers and the temporaries `t0`, `t1`
only (`toBs` and `fromBs` only `t0`), and slots of the scratch buffer at
`r9` for masks.
-/

namespace VG.Impl.Aes.X86_64

open VG.X86_64

def rorI (d : Reg) (n : Nat) : Instr := .shift .ror d n
def shrI (d : Reg) (n : Nat) : Instr := .shift .shr d n
def imm (d : Reg) (v : BitVec 64) : Instr := .movImm64 d v

/-! ## Between bytes and the bitsliced state -/

/-- A delta swap within `x`: exchanges the bits of `x` in the mask held in
slot `m` with the bits `s` places above them (`t` is clobbered). -/
def swapIn (x t : Reg) (m s : Nat) : List Instr :=
  [movR t x, shrI t s, xorR t x, andS t m, xorR x t, rorI t (64 - s), xorR x t]

/-- A delta swap between `x` and `y` (BearSSL's `SWAPN`): exchanges the bits
of `y` in the mask held in slot `m` with the bits of `x` `s` places above them. -/
def swapBetween (x y t : Reg) (m s : Nat) : List Instr :=
  [movR t x, shrI t s, xorR t y, andS t m, xorR y t, rorI t (64 - s), xorR x t]

/-- The masks of the transposes, in slots 1–6. -/
def bsMasks : List (Nat × BitVec 64) :=
  [(1, 0x00000000FFFF0000), (2, 0x0000FF000000FF00), (3, 0x00FF00FF00FF00FF),
   (4, 0x5555555555555555), (5, 0x3333333333333333), (6, 0x0F0F0F0F0F0F0F0F)]

def setMasks (ms : List (Nat × BitVec 64)) : List Instr :=
  ms.flatMap fun (k, m) => [imm t0 m, st k t0]

/-- Bytes `0 1 2 3 4 5 6 7` of each word become `0 4 1 5 2 6 3 7`. -/
def zip1 : List Instr := (List.range 8).flatMap fun k => swapIn (q k) t0 1 16
def zip2 : List Instr := (List.range 8).flatMap fun k => swapIn (q k) t0 2 8

/-- Interleave the bytes of `q b` and `q (b + 4)`. -/
def swap8 : List Instr := (List.range 4).flatMap fun b => swapBetween (q b) (q (b + 4)) t0 3 8

/-- BearSSL's `br_aes_ct64_ortho`: transposes the 8×8 bit matrix in each
byte position of the eight words. -/
def ortho : List Instr :=
  ([(0, 1), (2, 3), (4, 5), (6, 7)].flatMap fun (a, b) => swapBetween (q a) (q b) t0 4 1) ++
  ([(0, 2), (1, 3), (4, 6), (5, 7)].flatMap fun (a, b) => swapBetween (q a) (q b) t0 5 2) ++
  ([(0, 4), (1, 5), (2, 6), (3, 7)].flatMap fun (a, b) => swapBetween (q a) (q b) t0 6 4)

/-- From four blocks (block `b`'s bytes 0–7 in `q b` and 8–15 in `q (b + 4)`,
little-endian) to the bitsliced state. Uses only the temporary `t0`. -/
def toBs : List Instr := setMasks bsMasks ++ zip1 ++ zip2 ++ swap8 ++ ortho

/-- From the bitsliced state back to four blocks, as `toBs` takes them. -/
def fromBs : List Instr := setMasks bsMasks ++ ortho ++ swap8 ++ zip2 ++ zip1

/-! ## The round transformations -/

/-- The masks of ShiftRows, in slots 1–6. -/
def srMasks : List (Nat × BitVec 64) :=
  [(1, 0x0000FFFF0000FFFF), (2, 0x0FFF00000FFF0000), (3, 0xF0000000F0000000),
   (4, 0x00000000FFFFFFFF), (5, 0x00FF00FF00000000), (6, 0xFF00FF0000000000)]

/-- ShiftRows of one word: rows 1 and 3 rotate by 4 bits within their 16
bits, then rows 2 and 3 by 8. -/
def srWord (x : Reg) : List Instr :=
  [movR t0 x, rorI t0 4, andS t0 2, movR t1 x, rorI t1 52, andS t1 3,
   andS x 1, xorR x t0, xorR x t1,
   movR t0 x, rorI t0 8, andS t0 5, movR t1 x, rorI t1 56, andS t1 6,
   andS x 4, xorR x t0, xorR x t1]

def shiftRows : List Instr :=
  setMasks srMasks ++ (List.range 8).flatMap fun j => srWord (q j)

/-- The slot holding `u₇ = q₇ ⊕ (q₇ ⋙ 16)` during MixColumns. -/
def u7Slot : Nat := 7

/-- The register that output word `j` of MixColumns is computed in. -/
def mcOut (j : Nat) : Reg := if j = 0 then t0 else if j = 1 then t1 else q (j - 2)

/-- Output word `j` of MixColumns (BearSSL's `mix_columns`): with
`rⱼ = qⱼ ⋙ 16` (the next row) and `uⱼ = qⱼ ⊕ rⱼ`, it is
`uⱼ₋₁ ⊕ [j ∈ {0, 1, 3, 4}] u₇ ⊕ rⱼ ⊕ (uⱼ ⋙ 32)` (the multiplication by
`{02}` of `uⱼ` moves bit `j - 1` to `j` and reduces by `{1b}`). `q (j - 1)`
holds `uⱼ₋₁`, and `q j` is left holding `uⱼ`. -/
def mcWord (j : Nat) : List Instr :=
  [movR (mcOut j) (q j), rorI (mcOut j) 16, xorR (q j) (mcOut j)] ++
  (if j = 0 then [] else [xorR (mcOut j) (q (j - 1))]) ++
  (if j = 0 ∨ j = 1 ∨ j = 3 ∨ j = 4 then [xorS (mcOut j) u7Slot] else []) ++
  [rorI (q j) 32, xorR (mcOut j) (q j), rorI (q j) 32]

def mixColumns : List Instr :=
  [movR t0 (q 7), rorI t0 16, xorR t0 (q 7), st u7Slot t0] ++
  (List.range 8).flatMap mcWord ++
  ((List.range 8).reverse.map fun j => movR (q j) (mcOut j))

/-- The register pointing to the round key. -/
def kp : Reg := .rsi

/-- AddRoundKey, with the bitsliced round key at `kp`. -/
def addRoundKey : List Instr := (List.range 8).map fun j => .alu .xor (q j) (.mem (slotAt kp j))

end VG.Impl.Aes.X86_64
