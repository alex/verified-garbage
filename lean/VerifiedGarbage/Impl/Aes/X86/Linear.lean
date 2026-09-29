import VerifiedGarbage.Impl.Aes.X86.Sbox

/-!
# The linear layers of bitsliced AES on x86 (32-bit)

The state of two blocks is eight 32-bit words in slots `0 … 7` of the
scratch buffer at `edi`, word `j` holding bit `j` of the 32 bytes: byte
`i = r + 4c` (row `r`, column `c`) of block `b` is at bit position
`8r + 2c + b`, as in BearSSL's `aes_ct` (Thomas Pornin, MIT licence), whose
`ortho`, `shift_rows` and `mix_columns` these follow. So ShiftRows rotates
each 8-bit row, and MixColumns rotates whole words by 8 and 16 bits. The
model has no left shift: a left shift of bits that the mask has already
cleared at the top is a rotation.

Every block here uses the registers `tmpRegs` only, and slots `0 … 7`;
AddRoundKey also reads the round key at `esi`.
-/

namespace VG.Impl.Aes.X86

open VG.X86

def rorI (d : Reg) (n : Nat) : Instr := .shift .ror d n
def shrI (d : Reg) (n : Nat) : Instr := .shift .shr d n
def andI (d : Reg) (v : BitVec 32) : Instr := .alu .and d (.imm v)

/-! ## Between bytes and the bitsliced state -/

/-- A delta swap between slots `a` and `b` (BearSSL's `SWAPN`): exchanges the
bits of `b` in the mask `m` with the bits of `a` `s` places above them. -/
def swapN (a b : Nat) (m : BitVec 32) (s : Nat) : List Instr :=
  [movS .eax a, movS .ebx b, movR .ecx .eax, shrI .ecx s, xorR .ecx .ebx, andI .ecx m,
   xorR .ebx .ecx, rorI .ecx (32 - s), xorR .eax .ecx, st a .eax, st b .ebx]

/-- BearSSL's `br_aes_ct_ortho`: transposes the 8×8 bit matrix of each byte
position of the eight words. It is its own inverse: from two blocks (bytes
`4w … 4w + 3` of block `b` in slot `2w + b`, little-endian) to the bitsliced
state, and back. -/
def ortho : List Instr :=
  ([(0, 1), (2, 3), (4, 5), (6, 7)].flatMap fun (a, b) => swapN a b 0x55555555 1) ++
  ([(0, 2), (1, 3), (4, 6), (5, 7)].flatMap fun (a, b) => swapN a b 0x33333333 2) ++
  ([(0, 4), (1, 5), (2, 6), (3, 7)].flatMap fun (a, b) => swapN a b 0x0F0F0F0F 4)

/-! ## The round transformations -/

/-- ShiftRows of slot `j`: rows 1 and 3 rotate by 2 bits within their 8
bits, then rows 2 and 3 by 4. -/
def srWord (j : Nat) : List Instr :=
  [movS .eax j,
   movR .ebx .eax, rorI .ebx 2, andI .ebx 0x3F003F00, movR .ecx .eax, rorI .ecx 26,
   andI .ecx 0xC000C000, andI .eax 0x00FF00FF, xorR .eax .ebx, xorR .eax .ecx,
   movR .ebx .eax, rorI .ebx 4, andI .ebx 0x0F0F0000, movR .ecx .eax, rorI .ecx 28,
   andI .ecx 0xF0F00000, andI .eax 0x0000FFFF, xorR .eax .ebx, xorR .eax .ecx,
   st j .eax]

def shiftRows : List Instr := (List.range 8).flatMap srWord

/-- Output word `j` of MixColumns (BearSSL's `mix_columns`): with
`rⱼ = qⱼ ⋙ 8` (the next row) and `uⱼ = qⱼ ⊕ rⱼ`, it is
`uⱼ₋₁ ⊕ [j ∈ {0, 1, 3, 4}] u₇ ⊕ rⱼ ⊕ (uⱼ ⋙ 16)` (the multiplication by
`{02}` of `uⱼ` moves bit `j - 1` to `j` and reduces by `{1b}`). `ebp` holds
`u₇`, and `ecx` holds `uⱼ₋₁` and is left holding `uⱼ`. -/
def mcWord (j : Nat) : List Instr :=
  [movS .eax j, movR .ebx .eax, rorI .ebx 8, xorR .eax .ebx, movR .edx .eax, rorI .edx 16,
   xorR .ebx .edx] ++
  (if j = 0 then [] else [xorR .ebx .ecx]) ++
  (if j = 0 ∨ j = 1 ∨ j = 3 ∨ j = 4 then [xorR .ebx .ebp] else []) ++
  [st j .ebx, movR .ecx .eax]

def mixColumns : List Instr :=
  [movS .ebp 7, movR .edx .ebp, rorI .edx 8, xorR .ebp .edx] ++ (List.range 8).flatMap mcWord

/-- The register pointing to the round key. -/
def kp : Reg := .esi

/-- AddRoundKey, with the bitsliced round key at `kp`. -/
def addRoundKey : List Instr :=
  (List.range 8).flatMap fun j => [movS .eax j, .alu .xor .eax (.mem (slotAt kp j)), st j .eax]

end VG.Impl.Aes.X86
