import VerifiedGarbage.Impl.MlKem.AArch64.Compress

/-!
# ML-DSA on AArch64: arithmetic modulo `q`

Pieces of code that the ML-DSA arithmetic functions share, for
`q = 8380417 < 2²³`. Coefficients are `u32`s, loaded with `ldr w` (which
zero-extends them) and computed on in 64-bit registers, where no
intermediate value wraps. The model has no flags, conditional select,
`umulh` or register-offset addressing (`TCB/AArch64/Isa.lean`): pointers
advance by an immediate, loops count down to zero (`cbnz`), and conditional
steps use the sign bit of a 64-bit difference.

* `csub d t qr` (ML-KEM's, `Impl/MlKem/AArch64/Basic.lean`): `d ← d mod q`
  for `d < 2q`, with `q` in `qr`: `d - q`, plus `q` times its sign bit;
* `reduce d t`: `d ← d mod q` for `d < q²` (a product of two reduced values,
  or such a product plus a reduced value), by a Barrett reduction with
  64-bit products only: `t = ⌊⌊d / 2²²⌋ · M / 2⁴⁰⌋` for
  `M = ⌊2⁶² / q⌋` (in `x11`, so `⌊d / 2²²⌋ · M < 2⁶⁴`) is `⌊d / q⌋` or one
  less, so `d - t · q` (`madd` with `-q mod 2⁶⁴` in `x10`) is less than
  `2q`, and `csub` (with `q` in `x9`) reduces it. The multiplies' timing
  does not depend on their operands (FEAT_DIT lists MADD);
* `consts`: `q` in `x9`, `-q mod 2⁶⁴` in `x10` and `M` in `x11`;
* `storeTab t n b`: the table `t 0, …, t (n - 1)` of constants stored as
  `u32`s at `b` (in the working space), through `x9`.
-/

namespace VG.Impl.MlDsa.AArch64.Arith

open VG.AArch64
open VG.Impl.MlKem.AArch64 (mov csub movImm)

/-- `q = 8380417`. -/
def qNat : Nat := 8380417

/-- `M = ⌊2⁶² / q⌋`. -/
def barrettM : Nat := 550293143936

/-- `-q mod 2⁶⁴`. -/
def negQ : BitVec 64 := BitVec.ofNat 64 (2 ^ 64 - 8380417)

/-- A word `v` into `d`: `movz` of its low half, then `movk` of its high half. -/
def movW (d : Reg) (v : BitVec 32) : List Instr :=
  [.movz .w d (v.extractLsb' 0 16) 0, .movk .w d (v.extractLsb' 16 16) 1]

/-- `q` in `x9`, `-q mod 2⁶⁴` in `x10`, `M` in `x11`. -/
def consts : List Instr :=
  movW .x9 (BitVec.ofNat 32 qNat) ++ movImm .x10 negQ ++ movImm .x11 (BitVec.ofNat 64 barrettM)

/-- `d ← d mod q` for `d < q²`, with a temporary `t`, and `q`, `-q` and `M` in
`x9`, `x10` and `x11`. -/
def reduce (d t : Reg) : List Instr :=
  [.lsr .x t d 22, .mul .x t t .x11, .lsr .x t t 40, .madd .x d t .x10 d] ++ csub d t .x9

/-- `t i` to `[b + 4i]`, through `x9`. -/
def tabStep (t : Nat → Nat) (b : Reg) (i : Nat) : List Instr :=
  movW .x9 (BitVec.ofNat 32 (t i)) ++ [.str .w .x9 b (4 * i)]

/-- The table `t 0, …, t (n - 1)` at `b`. -/
def storeTab (t : Nat → Nat) (n : Nat) (b : Reg) : List Instr := (List.range n).flatMap (tabStep t b)

end VG.Impl.MlDsa.AArch64.Arith
