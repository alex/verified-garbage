import VerifiedGarbage.Impl.MlKem.AArch64.Compress

/-!
# ML-DSA on AArch64: packing and unpacking `d`-bit fields

The encodings of FIPS 204 §7.1 (`SimpleBitPack`, `BitPack`, `BitUnpack`, and
`SimpleBitUnpack` in `t₁ · 2ᵈ`) write each coefficient as a `d`-bit
little-endian field. The code handles each width `d` (chosen by a public
length, or fixed) with the same loops, parametrized by `d`: a group of `c`
coefficients is `nb` bytes (`d · c = 8 · nb`), and a loop runs over the
`256 / c` groups with `x11` counting down to zero (`cbnz`). Within a group,
the fields stream through the accumulator `x9`, in a schedule that depends
only on `d`:

* `packBody ld d c nb` (coefficients at `x0`, bytes to `x2`): the value of
  coefficient `j` (`ld j`, into `x10`, at most `d` bits) is added to `x9`
  above the `d·j mod 8` bits `x9` holds (`lsl`, then `add`), and then each
  byte it completes, the low byte of `x9`, is stored (`strb`) and shifted
  out (`lsr`).
* `unpackBody fin d c nb` (bytes at `x0`, coefficients to `x4`, the mask
  `2ᵈ - 1` in `x15`): before coefficient `j`, the bytes it needs are loaded
  (`ldrb`) and added to `x9` above the bits it holds; the field is then the
  low `d` bits of `x9` (into `x10`, and `x9` shifted right by `d`), which
  `fin j` turns into the coefficient and stores.

`x9` never holds more than `d + 7` bits. Every address and branch depends
only on the pointers and `d`.
-/

namespace VG.Impl.MlDsa.AArch64.Pack

open VG.AArch64
open VG.Impl.MlKem.AArch64 (movImm)

/-- `q = 8380417`. -/
def qNat : Nat := 8380417

/-- `x9 ← x9 + x10 · 2^sh`, for `x10 < 2^(64 - sh)`. -/
def shiftAdd (sh : Nat) : List Instr :=
  (if sh = 0 then [] else [.lsl .x .x10 .x10 sh]) ++ [.add .x .x9 .x9 .x10]

/-! ## Packing -/

/-- Byte `t` of the group, the low byte of `x9`, to `[x2 + t]`. -/
def packByte (t : Nat) : List Instr := [.strb .x9 .x2 t, .lsr .x .x9 .x9 8]

/-- Coefficient `j` of the group: its value (`ld j`) into `x9`, then the
bytes it completes. -/
def packCoef (ld : Nat → List Instr) (d j : Nat) : List Instr :=
  ld j ++ shiftAdd (d * j % 8) ++
    (List.range (d * (j + 1) / 8 - d * j / 8)).flatMap fun u => packByte (d * j / 8 + u)

def packBody (ld : Nat → List Instr) (d c nb : Nat) : List Instr :=
  [.movz .x .x9 0 0] ++ (List.range c).flatMap (packCoef ld d) ++
    [.addImm .x .x0 .x0 (4 * c), .addImm .x .x2 .x2 nb, .subImm .x .x11 .x11 1]

/-- All the groups. -/
def packLoop (ld : Nat → List Instr) (d c nb : Nat) : Prog isa :=
  .seq (.block [.movz .x .x11 (BitVec.ofNat 16 (256 / c)) 0])
    (.loop (.block (packBody ld d c nb)) (.nonzero .x .x11))

/-! ## Unpacking -/

/-- The number of bytes of the group that the first `j` fields need. -/
def need (d j : Nat) : Nat := (d * j + 7) / 8

/-- Byte `t` of the group into `x9`, above the `8t - d·j` bits it holds. -/
def unpackByte (d j t : Nat) : List Instr := [.ldrb .x10 .x0 t] ++ shiftAdd (8 * t - d * j)

/-- Field `j` of the group: the bytes it needs into `x9`, then its value
into `x10`, and `fin j`. -/
def unpackCoef (fin : Nat → List Instr) (d j : Nat) : List Instr :=
  (List.range (need d (j + 1) - need d j)).flatMap (fun u => unpackByte d j (need d j + u)) ++
    [.logic .and .x .x10 .x9 .x15, .lsr .x .x9 .x9 d] ++ fin j

def unpackBody (fin : Nat → List Instr) (d c nb : Nat) : List Instr :=
  [.movz .x .x9 0 0] ++ (List.range c).flatMap (unpackCoef fin d) ++
    [.addImm .x .x0 .x0 nb, .addImm .x .x4 .x4 (4 * c), .subImm .x .x11 .x11 1]

/-- All the groups. -/
def unpackLoop (fin : Nat → List Instr) (d c nb : Nat) : Prog isa :=
  .seq (.block (movImm .x15 (BitVec.ofNat 64 (2 ^ d - 1)) ++ [.movz .x .x11 (BitVec.ofNat 16 (256 / c)) 0]))
    (.loop (.block (unpackBody fin d c nb)) (.nonzero .x .x11))

end VG.Impl.MlDsa.AArch64.Pack
