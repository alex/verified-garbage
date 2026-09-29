import VerifiedGarbage.Impl.MlKem.X86_64.Compress

/-!
# ML-KEM-1024 on x86-64: `vg_mlkem1024_compress_encode` and `vg_mlkem1024_decode_decompress`

The widths of ML-KEM-1024 (`d = 5` or `11`, a public argument: the code
branches on it), as `vg_mlkem_compress_encode` and
`vg_mlkem_decode_decompress` do the widths of ML-KEM-768
(`Impl/MlKem/X86_64/Compress.lean`): a group of 8 coefficients is `d`
bytes, and the loop runs over the 32 groups with `rcx` counting down. The
values of a group are the base-`2ᵈ` digits of a number whose bytes are the
group's bytes; the code handles it in segments that fit in the 64 bits of
`r10`: a segment is the number whose digits are some consecutive values of
the group (accumulated from the last), shifted right by `s` bits, whose
bytes are some consecutive bytes of the group.

* `d = 5`: one segment, the 8 values (40 bits) and the 5 bytes.
* `d = 11`: values 0–4 (55 bits), whose low 6 bytes are bytes 0–5; and
  values 4–7 (44 bits) shifted right by 4, whose 5 bytes are bytes 6–10.
  Value 4 is in both (compressed twice; its bytes read twice to decode).

`compressEncode(f = rdi, d = esi, out = rdx, len = rcx)` (`out` moved to
`r8`) compresses each coefficient `x` with a multiplication,
`Compress_d(x) = ((x · M_d + 261888) >> 19) mod 2ᵈ` (`M_d` in `r9`), and
`decodeDecompress(b = rdi, len = rsi, d = edx, f = rcx)` (`f` moved to
`rsi`) decompresses each value `y` with a multiplication by `q` (in `r9`),
`(q · y + 2ᵈ⁻¹) >> d`.

Every address and branch depends only on the pointers and `d`.
-/

namespace VG.Impl.MlKem1024.X86_64

open VG.X86_64 VG.Impl.MlKem.X86_64

/-- `M_d`, the multiplier of `Compress_d`. -/
def ceMul1024 (d : Nat) : Nat := if d = 5 then 5040 else 322542

/-- Coefficient `j` of the group at `rdi`, compressed, into `r10`. -/
def ceCoef1024 (d j : Nat) : List Instr :=
  [.mov32 .rax (.mem (at_ .rdi (4 * j))), .mul .r9, .alu .add .rax (.imm 261888), .shift .shr .rax 19,
    .alu32 .and .rax (.imm (BitVec.ofNat 32 (2 ^ d - 1))), .shift .ror .r10 (64 - d),
    .alu .add .r10 (.reg .rax)]

/-- Coefficients `o, …, o + c - 1` of the group, from the last, into `r10`. -/
def ceAcc (d o c : Nat) : List Instr :=
  [.mov32 .r10 (.imm 0)] ++ (List.range c).flatMap fun t => ceCoef1024 d (o + (c - 1 - t))

/-- The `nb` low bytes of `r10` to `[r8 + k0]`, …. -/
def ceSt (k0 nb : Nat) : List Instr := (List.range nb).flatMap fun k => ceStore (k0 + k)

/-- The next group. -/
def ceTail (b : Nat) : List Instr :=
  [.alu .add .rdi (.imm 32), .alu .add .r8 (.imm (BitVec.ofNat 32 b)), .alu .sub .rcx (.imm 1)]

def ceBody5 : List Instr := ceAcc 5 0 8 ++ ceSt 0 5 ++ ceTail 5

def ceBody11 : List Instr :=
  ceAcc 11 0 5 ++ ceSt 0 6 ++ ceAcc 11 4 4 ++ ([.shift .shr .r10 4] : List Instr) ++ ceSt 6 5 ++ ceTail 11

/-- The 32 groups, for the width `d`. -/
def ceLoop (d : Nat) (body : List Instr) : Prog isa :=
  .seq (.block [.mov .r9 (.imm (BitVec.ofNat 32 (ceMul1024 d)))])
    (.seq (.block [.mov32 .rcx (.imm 32)]) (.loop (.block body) .ne))

def compressEncode1024 : Prog isa :=
  .seq (.block [.mov32 .rsi (.reg .rsi), .mov .r8 (.reg .rdx), .alu32 .cmp .rsi (.imm 5)])
    (.ite .e (ceLoop 5 ceBody5) (ceLoop 11 ceBody11))

/-- Bytes `o, …, o + b - 1` of the group at `rdi`, from the last, into `r10`. -/
def ddLd (o b : Nat) : List Instr :=
  [.mov32 .r10 (.imm 0)] ++ (List.range b).flatMap fun t => ddByte (o + (b - 1 - t))

/-- The low `c` values of `r10`, decompressed, to `[rsi + 4o]`, …. -/
def ddVals (d o c : Nat) : List Instr := (List.range c).flatMap fun j => ddCoef d (o + j)

/-- The next group. -/
def ddTail (b : Nat) : List Instr :=
  [.alu .add .rdi (.imm (BitVec.ofNat 32 b)), .alu .add .rsi (.imm 32), .alu .sub .rcx (.imm 1)]

def ddBody5 : List Instr := ddLd 0 5 ++ ddVals 5 0 8 ++ ddTail 5

def ddBody11 : List Instr :=
  ddLd 0 6 ++ ddVals 11 0 4 ++ ddLd 5 6 ++ ([.shift .shr .r10 4] : List Instr) ++ ddVals 11 4 4 ++ ddTail 11

/-- The 32 groups. -/
def ddLoop (body : List Instr) : Prog isa :=
  .seq (.block [.mov .r9 (.imm qImm)]) (.seq (.block [.mov32 .rcx (.imm 32)]) (.loop (.block body) .ne))

def decodeDecompress1024 : Prog isa :=
  .seq (.block [.mov32 .rdx (.reg .rdx), .mov .rsi (.reg .rcx), .alu32 .cmp .rdx (.imm 5)])
    (.ite .e (ddLoop ddBody5) (ddLoop ddBody11))

end VG.Impl.MlKem1024.X86_64
