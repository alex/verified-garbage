import VerifiedGarbage.Impl.X448.AArch64.Common

/-!
# Two Curve448 field multiplications in AdvSIMD

`mul2 o₁ a₁ b₁ o₂ a₂ b₂` computes `[o₁] := [a₁] * [b₁]` and
`[o₂] := [a₂] * [b₂]` at once, with operands and results in the scalar format
(eight radix-2⁵⁶ limbs, `Fast`), lane `e` of each vector holding element `e`.

Each operand is split into sixteen radix-2²⁸ limbs: vector `i` of an operand
holds limbs `2i` (32-bit lanes 0 and 1, one per element) and `2i + 1` (lanes 2
and 3). `umull`/`umlal` multiply limbs of the same parity, and `umull2`/`umlal2`
the next ones; a copy of the second operand shifted by one limb (`ext`) gives
the products of limbs of different parity. The product follows Karatsuba's
identity for `φ = 2²²⁴` (limb 8), as `Fast` does: 192 products for the two
multiplications, accumulated in 64-bit lanes. The coefficients' carries run in
radix 2²⁸, and the final carry, into limbs 1 and 5, in radix 2⁵⁶, so the limbs
are bounded as a scalar product's are.

The code uses every vector register (the callers save `v8`–`v15`), and no
general-purpose register but `x3`, the working space, and `x12`, which holds
`2²⁸ - 1` (as for `Fast`).
-/

namespace VG.Impl.Curve448.AArch64.Neon

open VG.AArch64
open VG.Impl.X448.AArch64 (ACC)

/-- Vector working space, past the scalar code's. -/
def NA : Nat := 4096
def NB : Nat := NA + 128
def NAS : Nat := NA + 256
def NBS : Nat := NA + 320
def NBP : Nat := NA + 384

def V (n : Nat) : VReg := VReg.ofNat n

def ldq (t : Nat) (off : Nat) : Instr := .ldrq (V t) .x3 off
def stq (t : Nat) (off : Nat) : Instr := .strq (V t) .x3 off
def vo (op : VOp) : Instr := .vop op

/-- `2²⁸ - 1` (from `x12`) in each 64-bit lane of `v30`, and zero in `v31`. -/
def consts : List Instr :=
  [vo (.dup .d2 (V 30) .x12), vo (.movi0 (V 31))]

/-- Split the limbs of `[x₁]` and `[x₂]` into the vectors at `dst`. -/
def convert (x₁ x₂ dst : Nat) (X Y P Q : Nat) : List Instr :=
  (List.range 4).flatMap fun k =>
    [ldq X (x₁ + 16 * k), ldq Y (x₂ + 16 * k),
      vo (.perm .trn1 .d2 (V P) (V X) (V Y)), vo (.perm .trn2 .d2 (V Q) (V X) (V Y))] ++
    [(P, 2 * k), (Q, 2 * k + 1)].flatMap fun (r, i) =>
      [vo (.logic .and (V X) (V r) (V 30)), vo (.shift .ushr .d2 (V Y) (V r) 28),
        vo (.perm .uzp1 .s4 (V r) (V X) (V Y)), stq r (dst + 16 * i)]

/-- The operand sums `a₀ + a₁` and `b₀ + b₁`. -/
def sums : List Instr :=
  (List.range 4).flatMap fun i =>
    [ldq 0 (NA + 16 * i), ldq 1 (NA + 16 * (i + 4)), vo (.add .s4 (V 0) (V 0) (V 1)), stq 0 (NAS + 16 * i),
      ldq 2 (NB + 16 * i), ldq 3 (NB + 16 * (i + 4)), vo (.add .s4 (V 2) (V 2) (V 3)), stq 2 (NBS + 16 * i)]

/-- The second operand of half `h` (0: `b₀`, 1: `b₁`, 2: `b₀ + b₁`). -/
def bHalf : Nat → Nat
  | 0 => NB
  | 1 => NB + 64
  | _ => NBS

/-- The first operand of half `h`. -/
def aHalf : Nat → Nat
  | 0 => NA
  | 1 => NA + 64
  | _ => NAS

/-- The second operand of each half shifted by one limb: vector `j + 1` holds
limbs `2j + 1` and `2j + 2` (`j = -1, …, 3`), zero past either end. -/
def shifted : List Instr :=
  (List.range 3).flatMap fun h =>
    ((List.range 4).map fun j => ldq j (bHalf h + 16 * j)) ++
    [vo (.ext (V 4) (V 31) (V 0) 8)] ++
    ((List.range 3).map fun j => vo (.ext (V (5 + j)) (V j) (V (j + 1)) 8)) ++
    [vo (.ext (V 8) (V 3) (V 31) 8)] ++
    ((List.range 5).map fun j => stq (4 + j) (NBP + 80 * h + 16 * j))

/-- The second-operand vectors: `0`–`3` the half, `4`–`8` the shifted ones. -/
def bOff (h bv : Nat) : Nat := if bv < 4 then bHalf h + 16 * bv else NBP + 80 * h + 16 * (bv - 4)

/-- One product of a half: limbs of `a` vector `i` times limbs of `b`
vector `bv`, the `2` form if `hi`, at coefficient `pos`. -/
structure Prod where
  hi : Bool
  i : Nat
  bv : Nat
  pos : Nat
  deriving DecidableEq, Repr

/-- The products of `a` vector `i`, by `b` vector. -/
def prodsOf (i : Nat) : List Prod :=
  ((List.range 4).flatMap fun j =>
    [⟨false, i, j, 2 * i + 2 * j⟩, ⟨true, i, j, 2 * i + 2 * j + 2⟩, ⟨false, i, 5 + j, 2 * i + 2 * j + 1⟩]) ++
  ((List.range 4).map fun j => ⟨true, i, 4 + j, 2 * i + 2 * j + 1⟩)

/-- All 64 products of a half, grouped by `b` vector. -/
def prods : List Prod :=
  (List.range 9).flatMap fun bv => ((List.range 4).flatMap prodsOf).filter (·.bv == bv)

/-- Accumulate a half product into `tgt pos`, starting the registers in `fresh`. -/
def mac (tgt : Nat → Nat) (fresh : List Nat) (seen : List Nat) (p : Prod) : Instr :=
  let d := tgt p.pos
  if d ∈ fresh ∧ d ∉ seen then vo (.umull p.hi (V d) (V (23 + p.i)) (V 27))
  else vo (.umlal p.hi (V d) (V (23 + p.i)) (V 27))

def macs (tgt : Nat → Nat) (fresh : List Nat) : List Prod → List Nat → List Instr
  | [], _ => []
  | p :: ps, seen => mac tgt fresh seen p :: macs tgt fresh ps (tgt p.pos :: seen)

/-- Load the `b` vector before its first product. -/
def withLoads (h : Nat) (tgt : Nat → Nat) (fresh : List Nat) : List Prod → List Nat → Option Nat → List Instr
  | [], _, _ => []
  | p :: ps, seen, cur =>
    (if cur = some p.bv then [] else [ldq 27 (bOff h p.bv)]) ++
      mac tgt fresh seen p :: withLoads h tgt fresh ps (tgt p.pos :: seen) (some p.bv)

/-- A half product. -/
def half (h : Nat) (tgt : Nat → Nat) (fresh : List Nat) : List Instr :=
  ((List.range 4).map fun i => ldq (23 + i) (aHalf h + 16 * i)) ++ withLoads h tgt fresh prods [] none

/-- After `S`: `r_d = S_d - S_{d+8}` in `v_d` and `r_{d+8} = -S_d` in `v_{d+8}`. -/
def foldS : List Instr :=
  ((List.range 7).flatMap fun d =>
    [vo (.mov (V 28) (V (d + 8))), vo (.sub .d2 (V (d + 8)) (V 31) (V d)), vo (.sub .d2 (V d) (V d) (V 28))]) ++
  [vo (.sub .d2 (V 15) (V 31) (V 7))]

/-- After `U`: `U_{d+8}` (in `v_{16+d}`) into both coefficients. -/
def foldU : List Instr :=
  (List.range 7).flatMap fun d =>
    [vo (.add .d2 (V d) (V d) (V (16 + d))), vo (.add .d2 (V (d + 8)) (V (d + 8)) (V (16 + d)))]

/-- The coefficients' carries in radix 2²⁸, `0 → 7` and `8 → 15`, then `7`
into 8 and `15` into 0 and 8. -/
def carries : List Instr :=
  ((List.range 7).flatMap fun k =>
    [(0, 28), (8, 29)].flatMap fun (b, t) =>
      [vo (.shift .ushr .d2 (V t) (V (b + k)) 28), vo (.logic .and (V (b + k)) (V (b + k)) (V 30)),
        vo (.add .d2 (V (b + k + 1)) (V (b + k + 1)) (V t))]) ++
  [vo (.shift .ushr .d2 (V 28) (V 7) 28), vo (.logic .and (V 7) (V 7) (V 30)),
    vo (.shift .ushr .d2 (V 29) (V 15) 28), vo (.logic .and (V 15) (V 15) (V 30)),
    vo (.add .d2 (V 8) (V 8) (V 28)), vo (.add .d2 (V 8) (V 8) (V 29)), vo (.add .d2 (V 0) (V 0) (V 29))]

/-- Radix-2⁵⁶ limbs in `v16`–`v23`, then the last carries into limbs 1 and 5
(`2⁵⁶ - 1` in `v31`), and the results. -/
def finish (o₁ o₂ : Nat) : List Instr :=
  ((List.range 8).flatMap fun i =>
    [vo (.shift .shl .d2 (V (16 + i)) (V (2 * i + 1)) 28), vo (.add .d2 (V (16 + i)) (V (16 + i)) (V (2 * i)))]) ++
  [vo (.shift .shl .d2 (V 31) (V 30) 28), vo (.add .d2 (V 31) (V 31) (V 30))] ++
  ([16, 20].flatMap fun i =>
    [vo (.shift .ushr .d2 (V 28) (V i) 56), vo (.logic .and (V i) (V i) (V 31)),
      vo (.add .d2 (V (i + 1)) (V (i + 1)) (V 28))]) ++
  (List.range 4).flatMap fun k =>
    [vo (.perm .trn1 .d2 (V 8) (V (16 + 2 * k)) (V (17 + 2 * k))),
      vo (.perm .trn2 .d2 (V 9) (V (16 + 2 * k)) (V (17 + 2 * k))), stq 8 (o₁ + 16 * k), stq 9 (o₂ + 16 * k)]

/-- `[o₁] := [a₁] * [b₁]` and `[o₂] := [a₂] * [b₂]`. -/
def mul2 (o₁ a₁ b₁ o₂ a₂ b₂ : Nat) : List Instr :=
  consts ++ convert a₁ a₂ NA 0 1 2 3 ++ convert b₁ b₂ NB 4 5 6 7 ++ sums ++ shifted ++
  half 0 (fun p => p) (List.range 15) ++ foldS ++
  half 1 (fun p => p) [] ++
  half 2 (fun p => if p < 8 then p + 8 else 16 + (p - 8)) ((List.range 7).map (16 + ·)) ++ foldU ++
  carries ++ finish o₁ o₂

end VG.Impl.Curve448.AArch64.Neon
