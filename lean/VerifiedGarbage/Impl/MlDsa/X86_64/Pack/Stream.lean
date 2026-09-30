import VerifiedGarbage.TCB.X86_64.Isa

/-!
# ML-DSA on x86-64: packing and unpacking `d`-bit fields

The encodings of FIPS 204 §7.1 (`SimpleBitPack`, `BitPack`, `BitUnpack`, and
`SimpleBitUnpack` in `t₁ · 2ᵈ`) write each coefficient as a `d`-bit
little-endian field. The code handles each width `d` (a public argument, or
fixed) with the same loops, parametrized by `d`: a group of `c`
coefficients is `nb` bytes (`d · c = 8 · nb`), and a loop runs over the
`256 / c` groups with `rcx` counting down. Within a group, the fields stream
through the accumulator `r10`, in a schedule that depends only on `d`:

* `packBody ld d c nb` (coefficients at `rdi`, bytes to `r8`): the value of
  coefficient `j` (`ld j`, into `rax`, at most `d` bits) is added to `r10`
  above the `d·j mod 8` bits `r10` holds (shifted left by rotating it right:
  its top bits are zero), and then each byte it completes, the low byte of
  `r10`, is stored and shifted out.
* `unpackBody fin d c nb` (bytes at `rdi`, coefficients to `rsi`): before
  coefficient `j`, the bytes it needs are added to `r10` above the bits it
  holds; the field is then the low `d` bits of `r10` (into `rax`, `r10`
  shifted right by `d`), which `fin j` turns into the coefficient and stores.

`r10` never holds more than `d + 7` bits. Every address and branch depends
only on the pointers and `d`.
-/

namespace VG.Impl.MlDsa.X86_64.Pack

open VG.X86_64

/-- `[b + d]`. -/
def at_ (b : Reg) (d : Nat) : MemOp := { base := b, disp := d }

/-- `q = 8380417`, as an immediate. -/
def qImm : BitVec 32 := 8380417

/-- `r10 ← r10 + rax · 2^sh`, for `rax < 2^(64 - sh)`. -/
def shiftAdd (sh : Nat) : List Instr :=
  (if sh = 0 then [] else [.shift .ror .rax (64 - sh)]) ++ [.alu .add .r10 (.reg .rax)]

/-! ## Packing -/

/-- Byte `t` of the group, the low byte of `r10`, to `[r8 + t]`. -/
def packByte (t : Nat) : List Instr := [.store8 (at_ .r8 t) .r10, .shift .shr .r10 8]

/-- Coefficient `j` of the group: its value (`ld j`) into `r10`, then the
bytes it completes. -/
def packCoef (ld : Nat → List Instr) (d j : Nat) : List Instr :=
  ld j ++ shiftAdd (d * j % 8) ++
    (List.range (d * (j + 1) / 8 - d * j / 8)).flatMap fun u => packByte (d * j / 8 + u)

def packBody (ld : Nat → List Instr) (d c nb : Nat) : List Instr :=
  [.mov32 .r10 (.imm 0)] ++ (List.range c).flatMap (packCoef ld d) ++
    [.alu .add .rdi (.imm (BitVec.ofNat 32 (4 * c))), .alu .add .r8 (.imm (BitVec.ofNat 32 nb)),
      .alu .sub .rcx (.imm 1)]

/-- All the groups. -/
def packLoop (ld : Nat → List Instr) (d c nb : Nat) : Prog isa :=
  .seq (.block [.mov32 .rcx (.imm (BitVec.ofNat 32 (256 / c)))]) (.loop (.block (packBody ld d c nb)) .ne)

/-! ## Unpacking -/

/-- The number of bytes of the group that the first `j` fields need. -/
def need (d j : Nat) : Nat := (d * j + 7) / 8

/-- Byte `t` of the group into `r10`, above the `8t - d·j` bits it holds. -/
def unpackByte (d j t : Nat) : List Instr := [.movzx8 .rax (at_ .rdi t)] ++ shiftAdd (8 * t - d * j)

/-- Field `j` of the group: the bytes it needs into `r10`, then its value
into `rax`, and `fin j`. -/
def unpackCoef (fin : Nat → List Instr) (d j : Nat) : List Instr :=
  (List.range (need d (j + 1) - need d j)).flatMap (fun u => unpackByte d j (need d j + u)) ++
    [.mov .rax (.reg .r10), .alu32 .and .rax (.imm (BitVec.ofNat 32 (2 ^ d - 1))), .shift .shr .r10 d] ++
    fin j

def unpackBody (fin : Nat → List Instr) (d c nb : Nat) : List Instr :=
  [.mov32 .r10 (.imm 0)] ++ (List.range c).flatMap (unpackCoef fin d) ++
    [.alu .add .rdi (.imm (BitVec.ofNat 32 nb)), .alu .add .rsi (.imm (BitVec.ofNat 32 (4 * c))),
      .alu .sub .rcx (.imm 1)]

/-- All the groups. -/
def unpackLoop (fin : Nat → List Instr) (d c nb : Nat) : Prog isa :=
  .seq (.block [.mov32 .rcx (.imm (BitVec.ofNat 32 (256 / c)))]) (.loop (.block (unpackBody fin d c nb)) .ne)

end VG.Impl.MlDsa.X86_64.Pack
