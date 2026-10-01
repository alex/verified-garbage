import VerifiedGarbage.Spec.Blake2
import VerifiedGarbage.Impl.Sha512.X86

/-!
# BLAKE2b compression function: x86 (32-bit) implementation

`vg_blake2b_compress(state, blocks, n, t, last, scratch)`, cdecl: the
arguments are at `[esp + 4]` (`state`), `[esp + 8]` (`blocks`), `[esp + 12]`
(`n`), `[esp + 16]` and `[esp + 20]` (the low and high halves of `t`),
`[esp + 24]` (`last`) and `[esp + 28]` (`scratch`).

* Each 64-bit word is a pair of 32-bit words, the low one first (as in
  memory: little-endian), as in `Impl/Sha512/X86.lean`, whose loads, stores
  and additions of such pairs (`ld`, `st`, `add64`, `add64m`) this uses. A
  rotation by 32 swaps the halves, which costs nothing: the code just names
  the registers the other way round. The model has no left shift, so a
  rotation of a pair by `0 < n < 32` rotates both halves right by `n`, then
  exchanges the bits that belong to the other half (the high `n` bits of
  each) through a mask (`rorPair`).
* With only seven usable registers, everything lives in `scratch` (`esi`),
  laid out as:
  - `[0, 128)`: a copy of the current block (word `j` at `8j`);
  - `[128, 256)`: the work vector `v` (word `k` at `128 + 8k`);
  - `[256, 288)`: the current block's address, the count of blocks left, the
    128-bit offset counter (four words, least significant first), and the
    final block flag as all-zero or all-one bits (twice, as a 64-bit word);
  - `[288, 304)`: the saved `ebx`, `esi`, `edi`, `ebp`.
* Each `G` loads the words it needs into the pairs `(eax, ebx)`,
  `(ecx, edx)` and `(edi, ebp)` and stores them back as soon as they are
  final for it (`g`). The rounds are fully unrolled.
* The hash value's address is read from its argument slot when needed. Every
  address is `esp`, `esi`, `ecx` (holding `state`) or `edi` (holding the
  block's address) plus a constant, and the only branches are on the count
  of blocks, so only the pointers, `n`, `t` and `last` can affect timing.
-/

namespace VG.Impl.Blake2.X86.CompressB

open VG.X86
open VG.Impl.Sha512.X86 (at_ sc ld st add64 add64m lo hi)

/-- `++`, grouping to the right. The kernel evaluates the code (for the
constant-time analysis), and `(a ++ b) ++ c` has it copy `a` twice. -/
local infixr:65 " +++ " => HAppend.hAppend

/-! ## The layout of `scratch` -/

/-- Word `j` of the copy of the block. -/
def msgOff (j : Nat) : Nat := 8 * j
/-- Word `k` of the work vector. -/
def vOff (k : Nat) : Nat := 128 + 8 * k
/-- The current block's address. -/
def blOff : Nat := 256
/-- The count of blocks left. -/
def nOff : Nat := 260
/-- The offset counter: its low 64 bits, then its high 64 bits. -/
def tOff : Nat := 264
/-- The final block flag (all-zero or all-one bits), as a 64-bit word. -/
def fOff : Nat := 280

/-! ## 64-bit operations on register pairs -/

/-- `(dl, dh) := (dl, dh) ^ (l, h)` -/
def xor64 (dl dh l h : Reg) : List Instr := [.alu .xor dl (.reg l), .alu .xor dh (.reg h)]

/-- The mask of the low `32 - n` bits. -/
def mask (n : Nat) : BitVec 32 := BitVec.allOnes 32 >>> n

/-- Rotate the 64-bit word in the pair `(l, h)` right by `n` (`0 < n < 32`),
with `t` as a temporary: the result is in `(h, l)` (its low half in `h`).
Rotating each half right by `n` leaves its low `32 - n` bits where they
belong, and its high `n` bits in place of the other half's. -/
def rorPair (l h : Reg) (n : Nat) (t : Reg) : List Instr :=
  [.shift .ror l n, .shift .ror h n, .mov t (.reg l), .alu .xor t (.reg h),
    .alu .and t (.imm (mask n)), .alu .xor l (.reg t), .alu .xor h (.reg t)]

/-! ## The rounds -/

/-- `G` (RFC 7693 §3.1) on the words of the work vector at offsets `a, b, c,
d` of `scratch`, with the message words at offsets `x` and `y`. The rotation
by 32 is the swap of the halves of `(ecx, edx)`, and that by 63 a swap and a
rotation by 31. -/
def g (a b c d x y : Nat) : List Instr :=
  -- a := a + b + x, in (eax, ebx)
  ld .eax .ebx a +++ add64m .eax .ebx b +++ add64m .eax .ebx x +++
  -- d := (d ^ a) >>> 32, in (edx, ecx)
  ld .ecx .edx d +++ xor64 .ecx .edx .eax .ebx +++
  -- c := c + d, in (edi, ebp)
  ld .edi .ebp c +++ add64 .edi .ebp .edx .ecx +++ st .edx .ecx d +++
  -- b := (b ^ c) >>> 24, in (edx, ecx)
  ld .ecx .edx b +++ xor64 .ecx .edx .edi .ebp +++ st .edi .ebp c +++ rorPair .ecx .edx 24 .edi +++
  -- a := a + b + y
  add64 .eax .ebx .edx .ecx +++ add64m .eax .ebx y +++
  -- d := (d ^ a) >>> 16, in (ebp, edi)
  ld .edi .ebp d +++ xor64 .edi .ebp .eax .ebx +++ st .eax .ebx a +++ rorPair .edi .ebp 16 .eax +++
  -- c := c + d, in (eax, ebx)
  ld .eax .ebx c +++ add64 .eax .ebx .ebp .edi +++ st .ebp .edi d +++
  -- b := (b ^ c) >>> 63, in (edx, ecx)
  xor64 .edx .ecx .eax .ebx +++ st .eax .ebx c +++ rorPair .ecx .edx 31 .eax +++ st .edx .ecx b

/-- `G(v, x, y, z, u, m[s[2i]], m[s[2i+1]])` of round `r` (the `i`-th `G` of the
round). -/
def gAt (r i x y z u : Nat) : Prog isa :=
  .block (g (vOff x) (vOff y) (vOff z) (vOff u) (msgOff (Spec.Blake2.sigmaAt r (2 * i)))
    (msgOff (Spec.Blake2.sigmaAt r (2 * i + 1))))

/-- Round `r` (RFC 7693 §3.2). -/
def round (r : Nat) : Prog isa :=
  .seq (gAt r 0 0 4 8 12) <| .seq (gAt r 1 1 5 9 13) <| .seq (gAt r 2 2 6 10 14) <|
  .seq (gAt r 3 3 7 11 15) <| .seq (gAt r 4 0 5 10 15) <| .seq (gAt r 5 1 6 11 12) <|
  .seq (gAt r 6 2 7 8 13) (gAt r 7 3 4 9 14)

/-- Rounds `0 … n-1`. -/
def rounds : Nat → Prog isa
  | 0 => .block []
  | n + 1 => .seq (rounds n) (round n)

/-! ## One block -/

/-- Copy the `n` 32-bit words at `[src + so]` to `[esi + d]`, through `eax`. -/
def copyWords (src : Reg) (so d n : Nat) : List Instr :=
  (List.range n).flatMap fun j =>
    [.mov .eax (.mem (at_ src (so + 4 * j))), .store (at_ .esi (d + 4 * j)) .eax]

/-- Copy the block at `blocks` (loaded into `edi`) to `scratch[0..128)`. -/
def copy : List Instr := .mov .edi (sc blOff) :: copyWords .edi 0 0 32

/-- Word `k` of the work vector := the constant `v`. -/
def ivWord (k : Nat) (v : BitVec 64) : List Instr :=
  [.mov .eax (.imm (lo v)), .store (at_ .esi (vOff k)) .eax,
    .mov .eax (.imm (hi v)), .store (at_ .esi (vOff k + 4)) .eax]

/-- Word `k` of the work vector := the constant `v` ^ the word at `[esi + o]`. -/
def ivXor (k : Nat) (v : BitVec 64) (o : Nat) : List Instr :=
  [.mov .eax (.imm (lo v)), .alu .xor .eax (sc o), .store (at_ .esi (vOff k)) .eax,
    .mov .eax (.imm (hi v)), .alu .xor .eax (sc (o + 4)), .store (at_ .esi (vOff k + 4)) .eax]

/-- Initialize the work vector (RFC 7693 §3.2): the state (at `ecx`, loaded
from its argument slot), then the IV, with the offset counter and the final
block flag. -/
def init : List Instr :=
  .mov .ecx (.mem (at_ .esp 4)) :: copyWords .ecx 0 (vOff 0) 16 +++
  ivWord 8 Spec.Blake2.b.IV[0] +++ ivWord 9 Spec.Blake2.b.IV[1] +++
  ivWord 10 Spec.Blake2.b.IV[2] +++ ivWord 11 Spec.Blake2.b.IV[3] +++
  ivXor 12 Spec.Blake2.b.IV[4] tOff +++ ivXor 13 Spec.Blake2.b.IV[5] (tOff + 8) +++
  ivXor 14 Spec.Blake2.b.IV[6] fOff +++ ivWord 15 Spec.Blake2.b.IV[7]

/-- `h[i] := h[i] ^ v[i] ^ v[i + 8]`, for the 32-bit word `j` of the state at
`ecx`. -/
def finishWord (j : Nat) : List Instr :=
  [.mov .eax (.mem (at_ .ecx (4 * j))), .alu .xor .eax (sc (vOff 0 + 4 * j)),
    .alu .xor .eax (sc (vOff 8 + 4 * j)), .store (at_ .ecx (4 * j)) .eax]

/-- XOR the two halves of the work vector into the state (at `ecx`, loaded
from its argument slot). -/
def finish : List Instr := .mov .ecx (.mem (at_ .esp 4)) :: (List.range 16).flatMap finishWord

/-- Advance to the next block and its offset counter (a 128-bit addition, the
carry going through the four words), and decrement the count of blocks
(setting ZF when it hits 0). -/
def advance : List Instr :=
  [.mov .eax (sc blOff), .alu .add .eax (.imm 128), .store (at_ .esi blOff) .eax,
    .mov .eax (sc tOff), .alu .add .eax (.imm 128), .store (at_ .esi tOff) .eax,
    .mov .eax (sc (tOff + 4)), .alu .adc .eax (.imm 0), .store (at_ .esi (tOff + 4)) .eax,
    .mov .eax (sc (tOff + 8)), .alu .adc .eax (.imm 0), .store (at_ .esi (tOff + 8)) .eax,
    .mov .eax (sc (tOff + 12)), .alu .adc .eax (.imm 0), .store (at_ .esi (tOff + 12)) .eax,
    .mov .eax (sc nOff), .alu .sub .eax (.imm 1), .store (at_ .esi nOff) .eax]

def body : Prog isa :=
  .seq (.block (copy +++ init)) (.seq (rounds 12) (.block (finish +++ advance)))

/-! ## The whole function -/

/-- The callee-saved registers, and where they are saved. -/
def saved : List (Reg × Nat) := [(.ebx, 288), (.esi, 292), (.edi, 296), (.ebp, 300)]

/-- Save the callee-saved registers, keep the arguments in `scratch` (the
high 64 bits of the counter start at 0; the flag is `0 - (0 < last)`, all one
bits if `last ≠ 0`), and set ZF if there are no blocks. -/
def prologue : List Instr :=
  [.mov .eax (.mem (at_ .esp 28))] +++
  saved.map (fun (r, d) => .store (at_ .eax d) r) +++
  [.mov .esi (.reg .eax),
    .mov .eax (.mem (at_ .esp 8)), .store (at_ .esi blOff) .eax,
    .mov .eax (.mem (at_ .esp 16)), .store (at_ .esi tOff) .eax,
    .mov .eax (.mem (at_ .esp 20)), .store (at_ .esi (tOff + 4)) .eax,
    .mov .eax (.imm 0), .store (at_ .esi (tOff + 8)) .eax, .store (at_ .esi (tOff + 12)) .eax,
    .mov .eax (.mem (at_ .esp 24)), .mov .ecx (.imm 0), .alu .cmp .ecx (.reg .eax),
    .alu .sbb .ecx (.reg .ecx), .store (at_ .esi fOff) .ecx, .store (at_ .esi (fOff + 4)) .ecx,
    .mov .eax (.mem (at_ .esp 12)), .store (at_ .esi nOff) .eax, .alu .test .eax (.reg .eax)]

/-- Restore the callee-saved registers (`esi`, the base, last). -/
def epilogue : List Instr :=
  [.mov .ebx (sc 288), .mov .edi (sc 296), .mov .ebp (sc 300), .mov .esi (sc 292)]

def compress : Prog isa :=
  .seq (.block prologue) (.seq (.ite .e (.block []) (.loop body .ne)) (.block epilogue))

end VG.Impl.Blake2.X86.CompressB
