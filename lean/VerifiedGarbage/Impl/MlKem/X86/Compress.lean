import VerifiedGarbage.Impl.MlKem.X86.Basic

/-!
# ML-KEM on x86 (32-bit): `vg_mlkem_compress_encode` and `vg_mlkem_decode_decompress`

Both are leaves (`leaf`) that branch on `d` (1, 4 or 10) to a loop over the
groups of coefficients that fill whole bytes, with `esi` at the input,
`edi` at the output and `ecx` the groups left.

* `compressEncode(f, d, out, len)`: `Compress_d(x) = ((x · M_d + 262080) >> 19) mod 2ᵈ`
  (`compOp`, with `mul`; `M_d` is `cmul d`). A group of `k` coefficients
  (`8 / d` of them for `d` = 1 and 4, one byte; 4 of them for `d` = 10, five
  bytes) is packed into `ebx` from its last coefficient down: `ebx ← ebx · 2ᵈ + c`
  (`accStep`; the model has no left shift, and `ror` by `32 - d` shifts left a
  value less than `2³²⁻ᵈ`). For `d` = 10 only the low two bits of the last
  coefficient go into `ebx`, whose four bytes are stored; its high eight bits
  (kept in `ebp`) are the fifth byte.
* `decodeDecompress(b, len, d, f)`: `Decompress_d(y) = (q · y + 2ᵈ⁻¹) >> d`
  (`decompOp`). A byte (for `d` = 1 and 4) is loaded into `ebx`, and
  coefficient `j` of it is `(ebx >> dj) mod 2ᵈ` (`unpackStep`). For `d` = 10,
  the four bytes of a group are combined into `ebx` (`ebx ← 2⁸ · ebx + b`),
  whose three low 10-bit fields are the first three coefficients; the fourth is
  `(ebx >> 30) + 4 · b₄`.

Every address and branch depends only on the pointers and `d`.
-/

namespace VG.Impl.MlKem.X86

open VG.X86

/-- `++`, grouping to the right. -/
local infixr:65 " +++ " => HAppend.hAppend

/-- The multiplier of the compress formula for `d`. -/
def cmul (d : Nat) : Nat := if d = 1 then 315 else if d = 4 then 2520 else 161271

/-! ## `compressEncode` -/

/-- `eax ← Compress_d(eax)`, with `edx` as a temporary. -/
def compOp (d : Nat) : List Instr :=
  [.mov .edx (.imm (BitVec.ofNat 32 (cmul d))), .mul .edx, .alu .add .eax (.imm 262080),
    .shift .shr .eax 19, .alu .and .eax (.imm (BitVec.ofNat 32 (2 ^ d - 1)))]

/-- `ebx ← ebx · 2ᵈ + Compress_d(f[j])`, with `esi` at `f`. -/
def accStep (d j : Nat) : List Instr :=
  .mov .eax (.mem (at_ .esi (4 * j))) :: compOp d +++
    [.shift .ror .ebx (32 - d), .alu .add .ebx (.reg .eax)]

/-- `accStep` for `j - 1` down to 0. -/
def accSteps (d : Nat) : Nat → List Instr
  | 0 => []
  | j + 1 => accStep d j +++ accSteps d j

/-- A byte of `k` coefficients of `d` bits (`d · k = 8`). -/
def packBody (d k : Nat) : List Instr :=
  .mov .eax (.mem (at_ .esi (4 * (k - 1)))) :: compOp d +++ .mov .ebx (.reg .eax) :: accSteps d (k - 1) +++
    [.store8 (at_ .edi 0) .bl, .alu .add .esi (.imm (BitVec.ofNat 32 (4 * k))),
      .alu .add .edi (.imm 1), .alu .sub .ecx (.imm 1)]

/-- Five bytes of four coefficients of 10 bits. -/
def pack10Body : List Instr :=
  .mov .eax (.mem (at_ .esi 12)) :: compOp 10 +++
  [.mov .ebp (.reg .eax), .mov .ebx (.reg .eax), .alu .and .ebx (.imm 3)] +++ accSteps 10 3 +++
  [.mov .eax (.reg .ebx), .store8 (at_ .edi 0) .al, .shift .shr .eax 8, .store8 (at_ .edi 1) .al,
    .shift .shr .eax 8, .store8 (at_ .edi 2) .al, .shift .shr .eax 8, .store8 (at_ .edi 3) .al,
    .shift .shr .ebp 2, .mov .eax (.reg .ebp), .store8 (at_ .edi 4) .al,
    .alu .add .esi (.imm 16), .alu .add .edi (.imm 5), .alu .sub .ecx (.imm 1)]

/-- `ecx = n`, and a loop of `body`. -/
def countedLoop (n : Nat) (body : List Instr) : Prog isa :=
  .seq (.block [.mov .ecx (.imm (BitVec.ofNat 32 n))]) (.loop (.block body) .ne)

/-- `esi = f`, `edi = out`, `eax = d`, and compare it with 1. -/
def ceInit : List Instr :=
  [.mov .esi (.mem (at_ .esp 20)), .mov .edi (.mem (at_ .esp 28)), .mov .eax (.mem (at_ .esp 24)),
    .alu .cmp .eax (.imm 1)]

def compressEncode : Prog isa :=
  leaf (.seq (.block ceInit)
    (.ite .e (countedLoop 32 (packBody 1 8))
      (.seq (.block [.alu .cmp .eax (.imm 4)])
        (.ite .e (countedLoop 128 (packBody 4 2)) (countedLoop 64 pack10Body)))))

/-! ## `decodeDecompress` -/

/-- `eax ← Decompress_d(eax)`, with `edx` as a temporary. -/
def decompOp (d : Nat) : List Instr :=
  [.mov .edx (.imm 3329), .mul .edx, .alu .add .eax (.imm (BitVec.ofNat 32 (2 ^ (d - 1)))),
    .shift .shr .eax d]

/-- `eax ← ebx >> s` (nothing for `s = 0`). -/
def shrFrom (s : Nat) : List Instr :=
  .mov .eax (.reg .ebx) :: if s = 0 then [] else [.shift .shr .eax s]

/-- `f[j] ← Decompress_d((ebx >> dj) mod 2ᵈ)`, with `edi` at `f`. -/
def unpackStep (d j : Nat) : List Instr :=
  shrFrom (d * j) +++ .alu .and .eax (.imm (BitVec.ofNat 32 (2 ^ d - 1))) :: decompOp d +++
    [.store (at_ .edi (4 * j)) .eax]

/-- `unpackStep` for `0 … k - 1`. -/
def unpackSteps (d : Nat) : Nat → List Instr
  | 0 => []
  | j + 1 => unpackSteps d j +++ unpackStep d j

/-- The `k` coefficients of `d` bits of a byte (`d · k = 8`). -/
def unpackBody (d k : Nat) : List Instr :=
  .movzx8 .ebx (at_ .esi 0) :: unpackSteps d k +++
    [.alu .add .esi (.imm 1), .alu .add .edi (.imm (BitVec.ofNat 32 (4 * k))), .alu .sub .ecx (.imm 1)]

/-- `ebx ← 2⁸ · ebx + b[j]`, with `esi` at `b`. -/
def byteStep (j : Nat) : List Instr :=
  [.movzx8 .eax (at_ .esi j), .shift .ror .ebx 24, .alu .add .ebx (.reg .eax)]

/-- Four coefficients of 10 bits from five bytes. -/
def unpack10Body : List Instr :=
  .movzx8 .ebx (at_ .esi 3) :: byteStep 2 +++ byteStep 1 +++ byteStep 0 +++ unpackSteps 10 3 +++
  [.mov .eax (.reg .ebx), .shift .shr .eax 30, .movzx8 .edx (at_ .esi 4), .alu .add .edx (.reg .edx),
    .alu .add .edx (.reg .edx), .alu .add .eax (.reg .edx)] +++ decompOp 10 +++
  [.store (at_ .edi 12) .eax, .alu .add .esi (.imm 5), .alu .add .edi (.imm 16), .alu .sub .ecx (.imm 1)]

/-- `esi = b`, `edi = f`, `eax = d`, and compare it with 1. -/
def ddInit : List Instr :=
  [.mov .esi (.mem (at_ .esp 20)), .mov .edi (.mem (at_ .esp 32)), .mov .eax (.mem (at_ .esp 28)),
    .alu .cmp .eax (.imm 1)]

def decodeDecompress : Prog isa :=
  leaf (.seq (.block ddInit)
    (.ite .e (countedLoop 32 (unpackBody 1 8))
      (.seq (.block [.alu .cmp .eax (.imm 4)])
        (.ite .e (countedLoop 128 (unpackBody 4 2)) (countedLoop 64 unpack10Body)))))

end VG.Impl.MlKem.X86
