import VerifiedGarbage.Spec.Sha3
import VerifiedGarbage.Impl.Sha3.Tables
import VerifiedGarbage.TCB.AArch64.Isa

/-!
# Keccak-f[1600]: AArch64 implementation

`vg_keccak_f1600(state = x0, scratch = x1)`.

The same structure as the x86-64 implementation. `scratch` (512 bytes) is
laid out as:

* `[0, 200)`: a second state, which the rounds alternate with `state`: each
  round reads one (`src`) and writes the other (`dst`), so after the 24
  rounds the result is back in `state`;
* `[200, 392)`: the 24 round constants, stored by the prologue (built with
  `movz`/`movk`).

A round keeps `src` in `x0`, `dst` in `x1`, a pointer to its round constant
in `x2` and the end of the round constants in `x3`, and swaps `x0` and `x1`
at its end. It computes the five column parities `C[x]` (θ) into `x4–x8`,
then `D[x]` into `x9–x13`; then, for each plane `y` of the output, the five
lanes `B[x]` of `π(ρ(θ(A)))` in that plane into `x4–x8`, and stores
`B[x] ⊕ (¬B[x+1] ∧ B[x+2])` (χ, and ι for lane 0), computed in `x14`, to
`dst`. The model has no `bic`, so `¬b ∧ c` is computed as `(b ∧ c) ⊕ c`.

Only caller-saved registers are used (`x0`–`x15`), so nothing is saved.
Every address is a pointer plus a constant, and the only branch is the
round loop's, which depends only on the pointers, so only the pointers can
affect timing.
-/

namespace VG.Impl.Sha3.AArch64

open VG.AArch64
open VG.Impl.Sha3 (rhoOff piSrc)

/-- `mov d, n` (as `add d, n, #0`). -/
def mov (d n : Reg) : Instr := .addImm .x d n 0

/-- The register of `C[x]`, and then of `B[x]`. -/
def creg (x : Nat) : Reg := [Reg.x4, .x5, .x6, .x7, .x8].getD x .x4

/-- The register of `D[x]`. -/
def dreg (x : Nat) : Reg := [Reg.x9, .x10, .x11, .x12, .x13].getD x .x9

/-- The temporary of θ and χ. -/
def T : Reg := .x14

/-- The register the round constant is loaded into. -/
def R : Reg := .x15

/-- `C[x] = A[x, 0] ⊕ … ⊕ A[x, 4]`. -/
def column (x : Nat) : List Instr :=
  [.ldr .x (creg x) .x0 (8 * x),
    .ldr .x T .x0 (8 * (x + 5)), .logic .eor .x (creg x) (creg x) T,
    .ldr .x T .x0 (8 * (x + 10)), .logic .eor .x (creg x) (creg x) T,
    .ldr .x T .x0 (8 * (x + 15)), .logic .eor .x (creg x) (creg x) T,
    .ldr .x T .x0 (8 * (x + 20)), .logic .eor .x (creg x) (creg x) T]

/-- `D[x] = ROTL¹(C[x + 1]) ⊕ C[x - 1]` (a rotation left by 1 is one right by 63). -/
def dcol (x : Nat) : List Instr :=
  [.ror .x (dreg x) (creg ((x + 1) % 5)) 63, .logic .eor .x (dreg x) (dreg x) (creg ((x + 4) % 5))]

/-- `B[x] = ROTL^ρ(A[piSrc x y] ⊕ D[(x + 3y) mod 5])` for plane `y`. -/
def laneB (x y : Nat) : List Instr :=
  [.ldr .x (creg x) .x0 (8 * piSrc x y),
    .logic .eor .x (creg x) (creg x) (dreg ((x + 3 * y) % 5))] ++
    if rhoOff (piSrc x y) = 0 then [] else [.ror .x (creg x) (creg x) (64 - rhoOff (piSrc x y))]

/-- Lane `(x, y)` of the output: `B[x] ⊕ ((B[x+1] ∧ B[x+2]) ⊕ B[x+2])`, and
for lane 0 the round constant at `x2`. -/
def chi (x y : Nat) : List Instr :=
  [.logic .and .x T (creg ((x + 1) % 5)) (creg ((x + 2) % 5)),
    .logic .eor .x T T (creg ((x + 2) % 5)), .logic .eor .x T T (creg x)] ++
    (if x = 0 ∧ y = 0 then [.ldr .x R .x2 0, .logic .eor .x T T R] else []) ++
    [.str .x T .x1 (8 * (x + 5 * y))]

/-- Plane `y` of the output. -/
def plane (y : Nat) : List Instr :=
  (List.range 5).flatMap (fun x => laneB x y) ++ (List.range 5).flatMap (fun x => chi x y)

/-- One round from `x0` to `x1`; then swap them, advance to the next round
constant, and set `x14` to zero after the last. -/
def round : List Instr :=
  (List.range 5).flatMap column ++ (List.range 5).flatMap dcol ++ (List.range 5).flatMap plane ++
    [mov T .x0, mov .x0 .x1, mov .x1 T, .addImm .x .x2 .x2 8, .sub .x T .x2 .x3]

/-- Round constant `k`, built in `R` and stored at `scratch + 200 + 8k`. -/
def rcStore (k : Nat) : List Instr :=
  [.movz .x R ((Spec.Sha3.RC k).extractLsb' 0 16) 0,
    .movk .x R ((Spec.Sha3.RC k).extractLsb' 16 16) 1,
    .movk .x R ((Spec.Sha3.RC k).extractLsb' 32 16) 2,
    .movk .x R ((Spec.Sha3.RC k).extractLsb' 48 16) 3,
    .str .x R .x1 (200 + 8 * k)]

/-- Store the round constants, and point `x2` at the first and `x3` past the
last. -/
def prologue : List Instr :=
  (List.range 24).flatMap rcStore ++ [.addImm .x .x2 .x1 200, .addImm .x .x3 .x1 392]

def permute : Prog isa :=
  .seq (.block prologue) (.loop (.block round) (.nonzero .x T))

end VG.Impl.Sha3.AArch64
