import VerifiedGarbage.Impl.X448.AArch64.Common

/-!
# Curve448 field arithmetic on AArch64, in registers

A field element is eight radix-2⁵⁶ limbs in eight words of a 128-byte slot.
A multiplication's operands stay in registers. Its eight coefficients follow
Karatsuba's identity for `φ = 2²²⁴`, `φ² = φ + 1 (mod p)`: with the halves
`S = a₀b₀`, `T = a₁b₁` and `U = (a₀ + a₁)(b₀ + b₁)`, coefficient `d < 4` is
`S_d + T_d + U_{d+4} - S_{d+4}` and coefficient `d + 4` is
`T_{d+4} + U_d + U_{d+4} - S_d`: 48 products (30 for a square), each
accumulated in a pair of registers. Coefficients `d` and `d + 4` are computed
together, and their carries pass to `d + 1` and `d + 5` while the next pair
is accumulated; the last two fold into limbs 0 and 4. The limbs are staged
and written at the end, so the output may be either operand.

Sums and differences are not reduced: their limbs only have to be small
enough for a multiplication's coefficients to fit in two words.
-/

namespace VG.Impl.Curve448.AArch64.Fast

open VG.AArch64
open VG.Impl.X448.AArch64 (ld st ACC TMP)

/-- Working words: the operand sums `a₀ + a₁` and `b₀ + b₁` of a product,
a square's doubled limbs, and the staged result. -/
def KA : Nat := ACC
def KB : Nat := ACC + 32
def KD : Nat := ACC + 64
def STAGE : Nat := TMP

/-- A multiplicand: a register, a word of the working space, or limb `k` of
the second operand (the slot `b` of `MOp.code`). -/
inductive Src
  | reg (r : Reg)
  | mem (d : Nat)
  | arg (k : Nat)
  deriving DecidableEq, Repr

/-- A two-word accumulator. -/
structure Acc where
  lo : Reg
  hi : Reg
  deriving DecidableEq, Repr

/-- The registers of a product's code. -/
structure Regs where
  /-- The low word of a product. -/
  t : Reg
  /-- A first multiplicand loaded from memory. -/
  p0 : Reg
  /-- A second multiplicand loaded from memory, and the high word of a product. -/
  p1 : Reg
  deriving DecidableEq, Repr

/-- One step of a column. -/
inductive MOp
  /-- `a := x * y` -/
  | set (a : Acc) (x y : Src)
  /-- `a := a + x * y` (or `-`) for each target `(a, add)` -/
  | prod (x y : Src) (ts : List (Acc × Bool))
  /-- `d := d + s` (or `-`) -/
  | merge (d s : Acc) (add : Bool)
  deriving DecidableEq, Repr

def Src.load (b : Nat) (r : Reg) : Src → List Instr
  | .reg _ => []
  | .mem d => [ld r d]
  | .arg k => [ld r (b + 8 * k)]

def Src.reg? (r : Reg) : Src → Reg
  | .reg q => q
  | _ => r

def addPair (d : Acc) (lo hi : Reg) (add : Bool) : List Instr :=
  if add then [.adds .x d.lo d.lo lo, .adcs .x d.hi d.hi hi]
  else [.subs .x d.lo d.lo lo, .sbcs .x d.hi d.hi hi]

def MOp.code (R : Regs) (b : Nat) : MOp → List Instr
  | .set a x y =>
    x.load b R.p0 ++ y.load b R.p1 ++
      [.mul .x a.lo (x.reg? R.p0) (y.reg? R.p1), .umulh a.hi (x.reg? R.p0) (y.reg? R.p1)]
  | .prod x y ts =>
    x.load b R.p0 ++ y.load b R.p1 ++
      [.mul .x R.t (x.reg? R.p0) (y.reg? R.p1), .umulh R.p1 (x.reg? R.p0) (y.reg? R.p1)] ++
      ts.flatMap fun a => addPair a.1 R.t R.p1 a.2
  | .merge d s add => addPair d s.lo s.hi add

/-! ## Columns -/

/-- The terms `(i, j)` of coefficient `e` of a product of four-limb halves. -/
def pairs (e : Nat) : List (Nat × Nat) :=
  ((List.range 4).filter fun i => i ≤ e ∧ e - i < 4).map fun i => (i, e - i)

/-- The terms of a square's coefficient `e`, each pair of distinct limbs once. -/
def sqPairs (e : Nat) : List (Nat × Nat) := (pairs e).filter fun p => p.1 ≤ p.2

/-- Accumulate the products of `ps` into `a`, starting it with the first. -/
def start (a : Acc) (ps : List (Src × Src)) (rest : List (Acc × Bool)) : List MOp :=
  match ps with
  | [] => []
  | (x, y) :: ps =>
    (if rest = [] then [.set a x y] else [.prod x y ((a, true) :: rest)]) ++
      ps.map fun (x, y) => .prod x y ((a, true) :: rest)

/-- Add products to targets, the first of which is not new. -/
def addTo (ps : List (Src × Src)) (ts : List (Acc × Bool)) : List MOp :=
  ps.map fun (x, y) => .prod x y ts

/-- A product of two shared sums: through a separate accumulator `s` when
there are several products, which then merges into each target. -/
def shared (s : Acc) (ps : List (Src × Src)) (ts : List (Acc × Bool)) : List MOp :=
  if 2 ≤ ps.length then start s ps [] ++ ts.map fun t => .merge t.1 s t.2
  else addTo ps ts

/-! ## Multiplication -/

namespace Mul

def A : Nat → Reg
  | 0 => .x0 | 1 => .x2 | 2 => .x4 | 3 => .x5 | 4 => .x6 | 5 => .x7 | 6 => .x8 | _ => .x9
def R : Regs := ⟨.x10, .x13, .x11⟩
def L : Acc := ⟨.x14, .x15⟩
def H : Acc := ⟨.x16, .x17⟩
def X : Acc := ⟨.x21, .x22⟩
def Y : Acc := ⟨.x27, .x28⟩

/-- The multiplicands of the products of half `h` (0: `S`, 1: `T`, 2: `U`). -/
def src (h : Nat) (p : Nat × Nat) : Src × Src :=
  match h with
  | 0 => (.reg (A p.1), .arg p.2)
  | 1 => (.reg (A (p.1 + 4)), .arg (p.2 + 4))
  | _ => (.mem (KA + 8 * p.1), .mem (KB + 8 * p.2))

def terms (h e : Nat) : List (Src × Src) := (pairs e).map (src h)

/-- Coefficients `d` (in `L`) and `d + 4` (in `H`). -/
def column (d : Nat) : List MOp :=
  start L (terms 1 d) [] ++
  start H (terms 1 (d + 4) ++ terms 2 d) [] ++
  shared Y (terms 2 (d + 4)) [(L, true), (H, true)] ++
  shared X (terms 0 d) [(L, true), (H, false)] ++
  addTo (terms 0 (d + 4)) [(L, false)]

end Mul

/-! ## Squaring -/

namespace Sqr

def A : Nat → Reg := Mul.A
def Z : Nat → Reg
  | 0 => .x10 | 1 => .x11 | 2 => .x13 | _ => .x14
def R : Regs := ⟨.x15, .x17, .x16⟩
def L : Acc := ⟨.x21, .x22⟩
def H : Acc := ⟨.x27, .x28⟩

/-- Limb `i` of half `h` (0: `a₀`, 1: `a₁`, 2: `a₀ + a₁`). -/
def limb (h i : Nat) : Reg := match h with
  | 0 => A i
  | 1 => A (i + 4)
  | _ => Z i

/-- A square's product `(i, j)`: a cross product doubles its first factor. -/
def src (h : Nat) (p : Nat × Nat) : Src × Src :=
  if p.1 = p.2 then (.reg (limb h p.1), .reg (limb h p.1))
  else (.mem (KD + 24 * h + 8 * p.1), .reg (limb h p.2))

def terms (h e : Nat) : List (Src × Src) := (sqPairs e).map (src h)

def column (d : Nat) : List MOp :=
  start L (terms 1 d) [] ++
  start H (terms 1 (d + 4) ++ terms 2 d) [] ++
  addTo (terms 2 (d + 4)) [(L, true), (H, true)] ++
  addTo (terms 0 d) [(L, true), (H, false)] ++
  addTo (terms 0 (d + 4)) [(L, false)]

end Sqr

/-! ## Carries -/

def CL : Reg := .x23
def CH : Reg := .x24
def MASK : Reg := .x25
def ZERO : Reg := .x26

/-- `(2⁵⁶ - 1, 0)` in `MASK` and `ZERO`. -/
def consts : List Instr :=
  [.movz .x MASK 0xffff 0, .movk .x MASK 0xffff 1, .movk .x MASK 0xffff 2,
    .movk .x MASK 0x00ff 3, .movz .x ZERO 0 0]

/-- Add the incoming carry `c` (unless `first`), stage limb `k`, and leave
the outgoing carry in `c`. -/
def colEnd (t : Reg) (a : Acc) (c : Reg) (first : Bool) (k : Nat) : List Instr :=
  (if first then [] else [.adds .x a.lo a.lo c, .adcs .x a.hi a.hi ZERO]) ++
  [.logic .and .x t a.lo MASK, st t (STAGE + 8 * k), .extr .x c a.hi a.lo 56]

/-- Fold the last carries, `CL` into limb 4 and `CH` into limbs 0 and 4, with
one more carry into limbs 1 and 5, and write the result. -/
def finish (o : Nat) : List Instr :=
  [ld .x4 STAGE, ld .x5 (STAGE + 8), ld .x6 (STAGE + 32), ld .x7 (STAGE + 40),
    .add .x .x4 .x4 CH, .add .x .x6 .x6 CH, .add .x .x6 .x6 CL,
    .lsr .x .x8 .x4 56, .logic .and .x .x4 .x4 MASK, .add .x .x5 .x5 .x8,
    .lsr .x .x8 .x6 56, .logic .and .x .x6 .x6 MASK, .add .x .x7 .x7 .x8,
    st .x4 o, st .x5 (o + 8), st .x6 (o + 32), st .x7 (o + 40)] ++
  [2, 3, 6, 7].flatMap fun i => [ld .x4 (STAGE + 8 * i), st .x4 (o + 8 * i)]

def columns (R : Regs) (b : Nat) (L H : Acc) (col : Nat → List MOp) : List Instr :=
  (List.range 4).flatMap fun d =>
    (col d).flatMap (MOp.code R b) ++ colEnd R.t L CL (d == 0) d ++ colEnd R.t H CH (d == 0) (d + 4)

/-- Load the limbs of `a` into `A 0`–`A 7`. -/
def loadA (a : Nat) : List Instr := (List.range 8).map fun i => ld (Mul.A i) (a + 8 * i)

/-- `[o] := [a] * [b]`. -/
def mul (o a b : Nat) : List Instr :=
  loadA a ++ consts ++
  (List.range 4).flatMap (fun i =>
    [.add .x Mul.R.p0 (Mul.A i) (Mul.A (i + 4)), st Mul.R.p0 (KA + 8 * i),
      ld Mul.R.t (b + 8 * i), ld Mul.R.p1 (b + 32 + 8 * i),
      .add .x Mul.R.t Mul.R.t Mul.R.p1, st Mul.R.t (KB + 8 * i)]) ++
  columns Mul.R b Mul.L Mul.H Mul.column ++ finish o

/-- `[o] := [a] * [a]`. -/
def sqr (o a : Nat) : List Instr :=
  loadA a ++ consts ++
  (List.range 4).map (fun i => .add .x (Sqr.Z i) (Sqr.A i) (Sqr.A (i + 4))) ++
  (List.range 3).flatMap (fun k => (List.range 3).flatMap fun h =>
    [.add .x Sqr.R.t (Sqr.limb h k) (Sqr.limb h k), st Sqr.R.t (KD + 24 * h + 8 * k)]) ++
  columns Sqr.R a Sqr.L Sqr.H Sqr.column ++ finish o

/-! ## Sums and differences -/

/-- Limb `i` of `2p`. -/
def twoP (i : Nat) : Nat := if i = 4 then 2 ^ 57 - 4 else 2 ^ 57 - 2

/-- `2p`'s limbs in `x0` (`2⁵⁷ - 2`) and `x2` (`2⁵⁷ - 4`). -/
def twoPRegs : List Instr :=
  [.movz .x .x0 0xfffe 0, .movk .x .x0 0xffff 1, .movk .x .x0 0xffff 2, .movk .x .x0 0x01ff 3,
    .movz .x .x2 0xfffc 0, .movk .x .x2 0xffff 1, .movk .x .x2 0xffff 2, .movk .x .x2 0x01ff 3]

def twoPReg (i : Nat) : Reg := if i = 4 then .x2 else .x0

/-- `[o] := [a] + 2p - [b]`. -/
def sub (o a b : Nat) : List Instr :=
  twoPRegs ++ (List.range 8).flatMap fun i =>
    [ld .x4 (a + 8 * i), ld .x5 (b + 8 * i), .add .x .x4 .x4 (twoPReg i),
      .sub .x .x4 .x4 .x5, st .x4 (o + 8 * i)]

/-- `[o₁] := [a] + [b]` and `[o₂] := [a] + 2p - [b]`. -/
def addSub (o₁ o₂ a b : Nat) : List Instr :=
  twoPRegs ++ (List.range 8).flatMap fun i =>
    [ld .x4 (a + 8 * i), ld .x5 (b + 8 * i), .add .x .x6 .x4 .x5, st .x6 (o₁ + 8 * i),
      .add .x .x7 .x4 (twoPReg i), .sub .x .x7 .x7 .x5, st .x7 (o₂ + 8 * i)]

/-- The ladder's sums and differences, `A = x₂ + z₂`, `B = x₂ - z₂`,
`C = x₃ + z₃`, `D = x₃ - z₃`, of the slots `x₂, z₂, x₃, z₃` swapped under
the mask in `x6`, which are left unswapped. -/
def butterfly (x2 z2 x3 z3 a b c d : Nat) : List Instr :=
  twoPRegs ++ (List.range 8).flatMap fun i =>
    [ld .x4 (x2 + 8 * i), ld .x7 (x3 + 8 * i), ld .x5 (z2 + 8 * i), ld .x8 (z3 + 8 * i),
      .logic .eor .x .x9 .x4 .x7, .logic .and .x .x9 .x9 .x6,
      .logic .eor .x .x4 .x4 .x9, .logic .eor .x .x7 .x7 .x9,
      .logic .eor .x .x9 .x5 .x8, .logic .and .x .x9 .x9 .x6,
      .logic .eor .x .x5 .x5 .x9, .logic .eor .x .x8 .x8 .x9,
      .add .x .x9 .x4 .x5, st .x9 (a + 8 * i),
      .add .x .x10 .x4 (twoPReg i), .sub .x .x10 .x10 .x5, st .x10 (b + 8 * i),
      .add .x .x11 .x7 .x8, st .x11 (c + 8 * i),
      .add .x .x13 .x7 (twoPReg i), .sub .x .x13 .x13 .x8, st .x13 (d + 8 * i)]

/-! ## Multiplication by `a24` -/

def smallC : Nat → Reg
  | 0 => .x4 | 1 => .x5 | 2 => .x6 | 3 => .x7 | 4 => .x8 | 5 => .x9 | 6 => .x10 | _ => .x11
def smallX : Nat → Reg
  | 0 => .x13 | 1 => .x14 | 2 => .x15 | 3 => .x16 | 4 => .x17 | 5 => .x21 | 6 => .x22 | _ => .x23

/-- Limb `i` of `a + 39081 e` before the carries: `a_i + 39081 e_i - 2⁵⁶ c_i`
(modulo 2⁶⁴), with the carry `c_i = ⌊39081 e_i / 2⁵⁶⌋` from `umulh` by
`39081 · 2⁸`. -/
def smallLimb (a e i : Nat) : List Instr :=
  [ld .x24 (e + 8 * i), ld (smallX i) (a + 8 * i),
    .madd .x (smallX i) .x24 .x0 (smallX i), .umulh (smallC i) .x24 .x2,
    .lsl .x .x24 (smallC i) 56, .sub .x (smallX i) (smallX i) .x24]

/-- `[o] := [a] + 39081 [e]`, with each carry added to the next limb and the
last to limbs 0 and 4. -/
def small (o a e : Nat) : List Instr :=
  [.movz .x .x0 39081 0, .movz .x .x2 0xa900 0, .movk .x .x2 0x0098 1] ++
  (List.range 8).flatMap (smallLimb a e) ++
  (List.range 8).flatMap fun i =>
    [.add .x (smallX i) (smallX i) (smallC ((i + 7) % 8))] ++
    (if i = 4 then [.add .x (smallX i) (smallX i) (smallC 7)] else []) ++
    [st (smallX i) (o + 8 * i)]

end VG.Impl.Curve448.AArch64.Fast
