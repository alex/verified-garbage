import VerifiedGarbage.Impl.MlKem.X86_64.Common

/-!
# ML-KEM on x86-64: `vg_mlkem_compress_encode` and `vg_mlkem_decode_decompress`

Both handle each width `d` (1, 4 or 10, a public argument: the code
branches on it) with the same code, parametrized by `d`: a group of `c`
coefficients is `b` bytes (`d · c = 8 · b`: 8 coefficients per byte for
`d = 1`, 2 per byte for `d = 4`, and 4 per 5 bytes for `d = 10`), and the
loop runs over the `256 / c` groups with `rcx` counting down. A group is
kept in `r10` as the number whose base-`2ᵈ` digits are its values, which
is also the number whose bytes are its bytes.

* `compressEncode(f = rdi, d = esi, out = rdx, len = rcx)` (`out` moved to
  `r8`): each coefficient `x` of the group, from the last, is compressed
  with a multiplication (`Compress_d(x) = ((x · M_d + 262080) >> 19) mod
  2ᵈ`, `M_d` in `r9`) and added to `r10` shifted left by `d` (rotated right
  by `64 - d`: its top bits are zero); then the `b` bytes of `r10` are
  stored.
* `decodeDecompress(b = rdi, len = rsi, d = edx, f = rcx)` (`f` moved to
  `rsi`): the `b` bytes of the group, from the last, are added to `r10`
  shifted left by 8; then each value, the low `d` bits of `r10` (which is
  then shifted right by `d`), is decompressed with a multiplication by `q`
  (in `r9`), `(q · y + 2ᵈ⁻¹) >> d`, and stored.

Every address and branch depends only on the pointers and `d`.
-/

namespace VG.Impl.MlKem.X86_64

open VG.X86_64

/-- `M_d`, the multiplier of `Compress_d`. -/
def ceMul (d : Nat) : Nat := if d = 1 then 315 else if d = 4 then 2520 else 161271

/-- Coefficient `j` of the group at `rdi`, compressed, into `r10`. -/
def ceCoef (d j : Nat) : List Instr :=
  [.mov32 .rax (.mem (at_ .rdi (4 * j))), .mul .r9, .alu .add .rax (.imm 262080), .shift .shr .rax 19,
    .alu32 .and .rax (.imm (BitVec.ofNat 32 (2 ^ d - 1))), .shift .ror .r10 (64 - d),
    .alu .add .r10 (.reg .rax)]

/-- Byte `k` of `r10` to `[r8 + k]`, then the next byte down. -/
def ceStore (k : Nat) : List Instr := [.store8 (at_ .r8 k) .r10, .shift .shr .r10 8]

def ceBody (d c b : Nat) : List Instr :=
  [.mov32 .r10 (.imm 0)] ++ (List.range c).flatMap (fun t => ceCoef d (c - 1 - t)) ++
    (List.range b).flatMap ceStore ++
    [.alu .add .rdi (.imm (BitVec.ofNat 32 (4 * c))), .alu .add .r8 (.imm (BitVec.ofNat 32 b)),
      .alu .sub .rcx (.imm 1)]

/-- All the groups, for the width `d`. -/
def ceLoop (d c b : Nat) : Prog isa :=
  .seq (.block [.mov .r9 (.imm (BitVec.ofNat 32 (ceMul d)))])
    (.seq (.block [.mov32 .rcx (.imm (BitVec.ofNat 32 (256 / c)))]) (.loop (.block (ceBody d c b)) .ne))

def compressEncode : Prog isa :=
  .seq (.block [.mov32 .rsi (.reg .rsi), .mov .r8 (.reg .rdx), .alu32 .cmp .rsi (.imm 1)])
    (.ite .e (ceLoop 1 8 1)
      (.seq (.block [.alu32 .cmp .rsi (.imm 4)]) (.ite .e (ceLoop 4 2 1) (ceLoop 10 4 5))))

/-- Byte `k` of the group at `rdi` into `r10`. -/
def ddByte (k : Nat) : List Instr :=
  [.movzx8 .rax (at_ .rdi k), .shift .ror .r10 56, .alu .add .r10 (.reg .rax)]

/-- Value `j` of the group, decompressed, to `[rsi + 4j]`. -/
def ddCoef (d j : Nat) : List Instr :=
  [.mov .rax (.reg .r10), .alu32 .and .rax (.imm (BitVec.ofNat 32 (2 ^ d - 1))), .mul .r9,
    .alu .add .rax (.imm (BitVec.ofNat 32 (2 ^ (d - 1)))), .shift .shr .rax d,
    .store32 (at_ .rsi (4 * j)) .rax, .shift .shr .r10 d]

def ddBody (d c b : Nat) : List Instr :=
  [.mov32 .r10 (.imm 0)] ++ (List.range b).flatMap (fun t => ddByte (b - 1 - t)) ++
    (List.range c).flatMap (ddCoef d) ++
    [.alu .add .rdi (.imm (BitVec.ofNat 32 b)), .alu .add .rsi (.imm (BitVec.ofNat 32 (4 * c))),
      .alu .sub .rcx (.imm 1)]

/-- All the groups, for the width `d`. -/
def ddLoop (d c b : Nat) : Prog isa :=
  .seq (.block [.mov .r9 (.imm qImm)])
    (.seq (.block [.mov32 .rcx (.imm (BitVec.ofNat 32 (256 / c)))]) (.loop (.block (ddBody d c b)) .ne))

def decodeDecompress : Prog isa :=
  .seq (.block [.mov32 .rdx (.reg .rdx), .mov .rsi (.reg .rcx), .alu32 .cmp .rdx (.imm 1)])
    (.ite .e (ddLoop 1 8 1)
      (.seq (.block [.alu32 .cmp .rdx (.imm 4)]) (.ite .e (ddLoop 4 2 1) (ddLoop 10 4 5))))

end VG.Impl.MlKem.X86_64
