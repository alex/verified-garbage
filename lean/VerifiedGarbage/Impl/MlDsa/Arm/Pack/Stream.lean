import VerifiedGarbage.TCB.Arm.Isa

/-!
# ML-DSA on 32-bit ARM: packing and unpacking `d`-bit fields

The encodings of FIPS 204 §7.1 (`SimpleBitPack`, `BitPack`, `BitUnpack`, and
`SimpleBitUnpack` in `t₁ · 2ᵈ`) write each coefficient as a `d`-bit
little-endian field. As on x86-64, each width `d` (a public argument, or
fixed) is handled by the same loops, parametrized by `d`: a group of `c`
coefficients is `nb` bytes (`d · c = 8 · nb`), and a loop runs over the
`256 / c` groups, counting down to zero with `subs` and `bne`. Within a
group, the fields stream through the accumulator `r3`, in a schedule that
depends only on `d`:

* `packBody ld d c nb` (coefficients at `r0`, bytes to `r2`, `r1`
  counting): the value of coefficient `j` (`ld j`, into `r12`, at most `d`
  bits; it may use `r4`) is added to `r3` shifted left by the `d·j mod 8`
  bits `r3` holds, and then each byte it completes, the low byte of `r3`, is
  stored and shifted out.
* `unpackBody fin d c nb` (bytes at `r0`, coefficients to `r1`, `r2`
  counting): before field `j`, each byte it needs (into `r12`) is added to
  `r3` shifted left by the bits `r3` holds; the field is then the low `d`
  bits of `r3` (into `r12`, by two shifts; `r3` shifted right by `d`), which
  `fin j` turns into the coefficient and stores (it may use `r4`).

`r3` never holds more than `d + 7 ≤ 27` bits, so it fits a register. Every
address and branch depends only on the pointers and `d`.
-/

namespace VG.Impl.MlDsa.Arm.Pack

open VG.Arm

/-- `r3 ← r3 + r12 · 2^sh`. -/
def shiftAdd (sh : Nat) : Instr :=
  .dp .add .r3 .r3 (if sh = 0 then .reg .r12 else .shifted .r12 .lsl sh)

/-! ## Packing -/

/-- Byte `t` of the group, the low byte of `r3`, to `[r2, #t]`. -/
def packByte (t : Nat) : List Instr := [.strb .r3 .r2 t, .mov .r3 (.shifted .r3 .lsr 8)]

/-- Coefficient `j` of the group: its value (`ld j`) into `r3`, then the
bytes it completes. -/
def packCoef (ld : Nat → List Instr) (d j : Nat) : List Instr :=
  ld j ++ [shiftAdd (d * j % 8)] ++
    (List.range (d * (j + 1) / 8 - d * j / 8)).flatMap fun u => packByte (d * j / 8 + u)

def packBody (ld : Nat → List Instr) (d c nb : Nat) : List Instr :=
  [.mov .r3 (.imm 0)] ++ (List.range c).flatMap (packCoef ld d) ++
    [.dp .add .r0 .r0 (.imm (BitVec.ofNat 32 (4 * c))), .dp .add .r2 .r2 (.imm (BitVec.ofNat 32 nb)),
      .subs .r1 .r1 (.imm 1)]

/-- All the groups. -/
def packLoop (ld : Nat → List Instr) (d c nb : Nat) : Prog isa :=
  .seq (.block [.mov .r1 (.imm (BitVec.ofNat 32 (256 / c)))]) (.loop (.block (packBody ld d c nb)) .ne)

/-! ## Unpacking -/

/-- The number of bytes of the group that the first `j` fields need. -/
def need (d j : Nat) : Nat := (d * j + 7) / 8

/-- Byte `t` of the group into `r3`, above the `8t - d·j` bits it holds. -/
def unpackByte (d j t : Nat) : List Instr :=
  [.ldrb .r12 .r0 t, .dp .add .r3 .r3 (if 8 * t - d * j = 0 then .reg .r12 else .shifted .r12 .lsl (8 * t - d * j))]

/-- The low `d` bits of `r3` into `r12`, and `r3` shifted right by `d`. -/
def extract (d : Nat) : List Instr :=
  [.mov .r12 (.shifted .r3 .lsl (32 - d)), .mov .r12 (.shifted .r12 .lsr (32 - d)), .mov .r3 (.shifted .r3 .lsr d)]

/-- Field `j` of the group: the bytes it needs into `r3`, then its value
into `r12`, and `fin j`. -/
def unpackCoef (fin : Nat → List Instr) (d j : Nat) : List Instr :=
  (List.range (need d (j + 1) - need d j)).flatMap (fun u => unpackByte d j (need d j + u)) ++ extract d ++
    fin j

def unpackBody (fin : Nat → List Instr) (d c nb : Nat) : List Instr :=
  [.mov .r3 (.imm 0)] ++ (List.range c).flatMap (unpackCoef fin d) ++
    [.dp .add .r0 .r0 (.imm (BitVec.ofNat 32 nb)), .dp .add .r1 .r1 (.imm (BitVec.ofNat 32 (4 * c))),
      .subs .r2 .r2 (.imm 1)]

/-- All the groups. -/
def unpackLoop (fin : Nat → List Instr) (d c nb : Nat) : Prog isa :=
  .seq (.block [.mov .r2 (.imm (BitVec.ofNat 32 (256 / c)))]) (.loop (.block (unpackBody fin d c nb)) .ne)

/-! ## Reduction modulo `q` -/

/-- `r := r + q` if `r` is negative (as a 32-bit two's complement number),
with `t` as a temporary: `m = r >> 31`, then `r + m + (m << 23) - (m << 13)`
(`q = 2²³ - 2¹³ + 1`). -/
def addQNeg (r t : Reg) : List Instr :=
  [.mov t (.shifted r .lsr 31), .dp .add r r (.reg t), .dp .add r r (.shifted t .lsl 23),
    .dp .sub r r (.shifted t .lsl 13)]

/-- `r := B - x` modulo `q`, for `x` in `x` (at most `q - 1 + B`, and `B`
at most `2¹⁹`): `B - x`, plus `q` if it is negative; `x` is overwritten. -/
def bMinus (B : Nat) (r x : Reg) : List Instr :=
  [.mov r (.imm (BitVec.ofNat 32 B)), .dp .sub r r (.reg x)] ++ addQNeg r x

end VG.Impl.MlDsa.Arm.Pack
