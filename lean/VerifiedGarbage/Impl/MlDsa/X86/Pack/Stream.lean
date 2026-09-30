import VerifiedGarbage.Impl.MlKem.X86.Basic

/-!
# ML-DSA on x86 (32-bit): packing and unpacking `d`-bit fields

The encodings of FIPS 204 §7.1 (`SimpleBitPack`, `BitPack`, `BitUnpack`, and
`SimpleBitUnpack` in `t₁ · 2ᵈ`) write each coefficient as a `d`-bit
little-endian field. As on x86-64, the code handles each width `d` (a public
argument, or fixed) with the same loops, parametrized by `d`: a group of `c`
coefficients is `nb` bytes (`d · c = 8 · nb`), and a loop runs over the
`256 / c` groups with `ecx` counting down. Within a group, the fields stream
through the accumulator `ebx`, in a schedule that depends only on `d`:

* `packBody ld d c nb` (coefficients at `esi`, bytes to `edi`): the value of
  coefficient `j` (`ld j`, into `eax`, at most `d` bits; `ld` may use `edx`)
  is added to `ebx` above the `d·j mod 8` bits `ebx` holds (shifted left by
  rotating it right: its top bits are zero), and then each byte it completes,
  `bl`, is stored and shifted out.
* `unpackBody fin d c nb` (bytes at `esi`, coefficients to `edi`): before
  coefficient `j`, the bytes it needs are added to `ebx` above the bits it
  holds; the field is then the low `d` bits of `ebx` (into `eax`, `ebx`
  shifted right by `d`), which `fin j` turns into the coefficient and stores
  (it may use `edx`).

`ebx` never holds more than `d + 7 ≤ 27` bits. Every address and branch
depends only on the pointers and `d`.
-/

namespace VG.Impl.MlDsa.X86.Pack

open VG.X86
open VG.Impl.MlKem.X86 (at_)

/-- `q = 8380417`, as an immediate. -/
def qImm : BitVec 32 := 8380417

/-- `ebx ← ebx + eax · 2^sh`, for `eax < 2^(32 - sh)`. -/
def shiftAdd (sh : Nat) : List Instr :=
  (if sh = 0 then [] else [.shift .ror .eax (32 - sh)]) ++ [.alu .add .ebx (.reg .eax)]

/-! ## Packing -/

/-- Byte `t` of the group, `bl`, to `[edi + t]`. -/
def packByte (t : Nat) : List Instr := [.store8 (at_ .edi t) .bl, .shift .shr .ebx 8]

/-- Coefficient `j` of the group: its value (`ld j`) into `ebx`, then the
bytes it completes. -/
def packCoef (ld : Nat → List Instr) (d j : Nat) : List Instr :=
  ld j ++ shiftAdd (d * j % 8) ++
    (List.range (d * (j + 1) / 8 - d * j / 8)).flatMap fun u => packByte (d * j / 8 + u)

def packBody (ld : Nat → List Instr) (d c nb : Nat) : List Instr :=
  [.mov .ebx (.imm 0)] ++ (List.range c).flatMap (packCoef ld d) ++
    [.alu .add .esi (.imm (BitVec.ofNat 32 (4 * c))), .alu .add .edi (.imm (BitVec.ofNat 32 nb)),
      .alu .sub .ecx (.imm 1)]

/-- All the groups. -/
def packLoop (ld : Nat → List Instr) (d c nb : Nat) : Prog isa :=
  .seq (.block [.mov .ecx (.imm (BitVec.ofNat 32 (256 / c)))]) (.loop (.block (packBody ld d c nb)) .ne)

/-! ## Unpacking -/

/-- The number of bytes of the group that the first `j` fields need. -/
def need (d j : Nat) : Nat := (d * j + 7) / 8

/-- Byte `t` of the group into `ebx`, above the `8t - d·j` bits it holds. -/
def unpackByte (d j t : Nat) : List Instr := [.movzx8 .eax (at_ .esi t)] ++ shiftAdd (8 * t - d * j)

/-- Field `j` of the group: the bytes it needs into `ebx`, then its value
into `eax`, and `fin j`. -/
def unpackCoef (fin : Nat → List Instr) (d j : Nat) : List Instr :=
  (List.range (need d (j + 1) - need d j)).flatMap (fun u => unpackByte d j (need d j + u)) ++
    [.mov .eax (.reg .ebx), .alu .and .eax (.imm (BitVec.ofNat 32 (2 ^ d - 1))), .shift .shr .ebx d] ++
    fin j

def unpackBody (fin : Nat → List Instr) (d c nb : Nat) : List Instr :=
  [.mov .ebx (.imm 0)] ++ (List.range c).flatMap (unpackCoef fin d) ++
    [.alu .add .esi (.imm (BitVec.ofNat 32 nb)), .alu .add .edi (.imm (BitVec.ofNat 32 (4 * c))),
      .alu .sub .ecx (.imm 1)]

/-- All the groups. -/
def unpackLoop (fin : Nat → List Instr) (d c nb : Nat) : Prog isa :=
  .seq (.block [.mov .ecx (.imm (BitVec.ofNat 32 (256 / c)))]) (.loop (.block (unpackBody fin d c nb)) .ne)

/-! ## Arguments and widths -/

/-- `esi` and `edi` from the arguments `i` and `o` of a leaf. -/
def ldPtrs (i o : Nat) : List Instr :=
  [.mov .esi (.mem (at_ .esp (20 + 4 * i))), .mov .edi (.mem (at_ .esp (20 + 4 * o)))]

/-- `ldPtrs`, and `eax` from the argument `w`. -/
def ldArgs (i o w : Nat) : List Instr := ldPtrs i o ++ [.mov .eax (.mem (at_ .esp (20 + 4 * w)))]

/-- `p` if `eax` is `v`, else `e`. -/
def sel (v : Nat) (p e : Prog isa) : Prog isa :=
  .seq (.block [.alu .cmp .eax (.imm (BitVec.ofNat 32 v))]) (.ite .e p e)

end VG.Impl.MlDsa.X86.Pack
