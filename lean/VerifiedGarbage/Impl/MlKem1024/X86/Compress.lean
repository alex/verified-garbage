import VerifiedGarbage.Impl.MlKem.X86.Compress

/-!
# ML-KEM-1024 on x86 (32-bit): `vg_mlkem1024_compress_encode` and `vg_mlkem1024_decode_decompress`

As `vg_mlkem_compress_encode` and `vg_mlkem_decode_decompress`
(`Impl/MlKem/X86/Compress.lean`), for `d` = 5 and 11: leaves (`leaf`) that
branch on `d` to a loop over the 32 groups of 8 coefficients, which fill
`d` bytes, with `esi` at the input, `edi` at the output and `ecx` the groups
left.

* `compressEncode(f, d, out, len)`: `Compress_d(x) = ((x · M_d + 261888) >> 19) mod 2ᵈ`
  (`cOp`; `M_d` is `cmul1024 d`). Words are packed into `ebx` from their last
  coefficient down (`accS`: `ebx ← ebx · 2ᵈ + c`, with `ror` by `32 - d` as the
  left shift) and stored byte by byte (`st4`, `st3`). For `d` = 5, `ebx` holds
  coefficients 0–5 and the low two bits of coefficient 6 (bytes 0–3), and `ebp`
  the high three bits of coefficient 6 and coefficient 7 (byte 4). For `d` = 11,
  three words: coefficients 0, 1 and the low ten bits of 2 (bytes 0–3); the
  high bit of 2 (kept in `ebp`), 3, 4 and the low nine bits of 5 (bytes 4–7);
  the high two bits of 5 (computed again), 6 and 7 (bytes 8–10).
* `decodeDecompress(b, len, d, f)`: `Decompress_d(y) = (q · y + 2ᵈ⁻¹) >> d`
  (`decompOp`). Up to four bytes of a group are combined into `ebx` (`ldW`),
  and a coefficient is a field of it (`fieldAt`: `(ebx >> s) mod 2ᵈ`), or a
  field that continues into the next byte (`crossAt`: the high bits of `ebx`
  plus the low bits of that byte, shifted left).

Every address and branch depends only on the pointers and `d`.
-/

namespace VG.Impl.MlKem1024.X86

open VG.X86 VG.Impl.MlKem.X86

/-- `++`, grouping to the right. -/
local infixr:65 " +++ " => HAppend.hAppend

/-- The multiplier of the compress formula for `d` = 5 and 11. -/
def cmul1024 (d : Nat) : Nat := if d = 5 then 5040 else 322542

/-! ## `compressEncode` -/

/-- `eax ← Compress_d(eax)`, with `edx` as a temporary. -/
def cOp (d : Nat) : List Instr :=
  [.mov .edx (.imm (BitVec.ofNat 32 (cmul1024 d))), .mul .edx, .alu .add .eax (.imm 261888),
    .shift .shr .eax 19, .alu .and .eax (.imm (BitVec.ofNat 32 (2 ^ d - 1)))]

/-- `eax ← Compress_d(f[j])`, with `esi` at `f`. -/
def ldC (d j : Nat) : List Instr := .mov .eax (.mem (at_ .esi (4 * j))) :: cOp d

/-- `ebx ← ebx · 2ᵈ + Compress_d(f[o + j])`. -/
def accS (d o j : Nat) : List Instr := ldC d (o + j) +++ [.shift .ror .ebx (32 - d), .alu .add .ebx (.reg .eax)]

/-- `accS` for `o + j - 1` down to `o`. -/
def accSs (d o : Nat) : Nat → List Instr
  | 0 => []
  | j + 1 => accS d o j +++ accSs d o j

/-- Store the four bytes of `ebx` at `edi + o`, through `eax`. -/
def st4 (o : Nat) : List Instr :=
  [.mov .eax (.reg .ebx), .store8 (at_ .edi o) .al, .shift .shr .eax 8, .store8 (at_ .edi (o + 1)) .al,
    .shift .shr .eax 8, .store8 (at_ .edi (o + 2)) .al, .shift .shr .eax 8, .store8 (at_ .edi (o + 3)) .al]

/-- Store the low three bytes of `ebx` at `edi + o`, through `eax`. -/
def st3 (o : Nat) : List Instr :=
  [.mov .eax (.reg .ebx), .store8 (at_ .edi o) .al, .shift .shr .eax 8, .store8 (at_ .edi (o + 1)) .al,
    .shift .shr .eax 8, .store8 (at_ .edi (o + 2)) .al]

/-- On to the next group of `c` coefficients and `b` bytes. -/
def nextG (c b : Nat) : List Instr :=
  [.alu .add .esi (.imm (BitVec.ofNat 32 c)), .alu .add .edi (.imm (BitVec.ofNat 32 b)), .alu .sub .ecx (.imm 1)]

/-- Five bytes of eight coefficients of 5 bits. -/
def pack5Body : List Instr :=
  ldC 5 7 +++ [.mov .ebp (.reg .eax), .shift .ror .ebp 29] +++
  ldC 5 6 +++ [.mov .ebx (.reg .eax), .alu .and .ebx (.imm 3), .shift .shr .eax 2, .alu .add .ebp (.reg .eax)] +++
  accSs 5 0 6 +++ st4 0 +++ [.mov .eax (.reg .ebp), .store8 (at_ .edi 4) .al] +++ nextG 32 5

/-- Eleven bytes of eight coefficients of 11 bits. -/
def pack11Body : List Instr :=
  ldC 11 2 +++ [.mov .ebp (.reg .eax), .shift .shr .ebp 10, .mov .ebx (.reg .eax), .alu .and .ebx (.imm 1023)] +++
  accSs 11 0 2 +++ st4 0 +++
  ldC 11 5 +++ [.mov .ebx (.reg .eax), .alu .and .ebx (.imm 511)] +++ accSs 11 3 2 +++
  [.shift .ror .ebx 31, .alu .add .ebx (.reg .ebp)] +++ st4 4 +++
  ldC 11 5 +++ [.shift .shr .eax 9, .mov .ebp (.reg .eax)] +++
  ldC 11 7 +++ [.mov .ebx (.reg .eax)] +++ accSs 11 6 1 +++
  [.shift .ror .ebx 30, .alu .add .ebx (.reg .ebp)] +++ st3 8 +++ nextG 32 11

/-- `esi = f`, `edi = out`, `eax = d`, and compare it with 5. -/
def ceInit5 : List Instr :=
  [.mov .esi (.mem (at_ .esp 20)), .mov .edi (.mem (at_ .esp 28)), .mov .eax (.mem (at_ .esp 24)),
    .alu .cmp .eax (.imm 5)]

def compressEncode : Prog isa :=
  leaf (.seq (.block ceInit5) (.ite .e (countedLoop 32 pack5Body) (countedLoop 32 pack11Body)))

/-! ## `decodeDecompress` -/

/-- `ebx ← 2⁸ · ebx + b[o + j]` for `j` from `n - 1` down to 0. -/
def bySteps (o : Nat) : Nat → List Instr
  | 0 => []
  | j + 1 => byteStep (o + j) +++ bySteps o j

/-- `ebx ←` the number whose base-2⁸ digits are the `n + 1` bytes at `esi + o`. -/
def ldW (o n : Nat) : List Instr := .movzx8 .ebx (at_ .esi (o + n)) :: bySteps o n

/-- `f[j] ← Decompress_d(eax)`, with `edi` at `f`. -/
def decSt (d j : Nat) : List Instr := decompOp d +++ [.store (at_ .edi (4 * j)) .eax]

/-- `f[j] ← Decompress_d((ebx >> s) mod 2ᵈ)`. -/
def fieldAt (d s j : Nat) : List Instr :=
  shrFrom s +++ .alu .and .eax (.imm (BitVec.ofNat 32 (2 ^ d - 1))) :: decSt d j

/-- `f[j] ← Decompress_d((ebx >> s) + 2ᵏ · (b[o] mod 2ᵉ))`. -/
def crossAt (d s o e k j : Nat) : List Instr :=
  [.movzx8 .edx (at_ .esi o), .alu .and .edx (.imm (BitVec.ofNat 32 (2 ^ e - 1))), .shift .ror .edx (32 - k),
    .mov .eax (.reg .ebx), .shift .shr .eax s, .alu .add .eax (.reg .edx)] +++ decSt d j

/-- Eight coefficients of 5 bits from five bytes. -/
def unpack5Body : List Instr :=
  ldW 0 3 +++ fieldAt 5 0 0 +++ fieldAt 5 5 1 +++ fieldAt 5 10 2 +++ fieldAt 5 15 3 +++ fieldAt 5 20 4 +++
  fieldAt 5 25 5 +++ crossAt 5 30 4 3 2 6 +++ ldW 4 0 +++ fieldAt 5 3 7 +++ nextG 5 32

/-- Eight coefficients of 11 bits from eleven bytes. -/
def unpack11Body : List Instr :=
  ldW 0 3 +++ fieldAt 11 0 0 +++ fieldAt 11 11 1 +++ crossAt 11 22 4 1 10 2 +++
  ldW 4 3 +++ fieldAt 11 1 3 +++ fieldAt 11 12 4 +++ crossAt 11 23 8 2 9 5 +++
  ldW 8 2 +++ fieldAt 11 2 6 +++ fieldAt 11 13 7 +++ nextG 11 32

/-- `esi = b`, `edi = f`, `eax = d`, and compare it with 5. -/
def ddInit5 : List Instr :=
  [.mov .esi (.mem (at_ .esp 20)), .mov .edi (.mem (at_ .esp 32)), .mov .eax (.mem (at_ .esp 28)),
    .alu .cmp .eax (.imm 5)]

def decodeDecompress : Prog isa :=
  leaf (.seq (.block ddInit5) (.ite .e (countedLoop 32 unpack5Body) (countedLoop 32 unpack11Body)))

end VG.Impl.MlKem1024.X86
