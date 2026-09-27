import VerifiedGarbage.Spec.Sha256
import VerifiedGarbage.TCB.AArch64.Isa

/-!
# SHA-256 compression function: AArch64 implementation

`vg_sha256_compress(state = x0, blocks = x1, n = x2, scratch = x3)`.

The same structure as the x86-64 implementation:
* The working variables `a … h` live in `w4`–`w11`; the fully unrolled rounds
  rename them: in round `t`, variable `k` is in `var t k`.
* The message schedule is a 16-word window in `scratch[0..64)`.
* Only caller-saved registers are used (`x0`–`x15`), so nothing is saved.
* `x0`–`x3` (the pointers and the block count) are public; no address and
  no branch depends on anything else.
-/

namespace VG.Impl.Sha256.AArch64

open VG.AArch64
open VG.Spec.Sha256 (K)

/-- The registers holding the working variables. -/
def work : List Reg := [.x4, .x5, .x6, .x7, .x8, .x9, .x10, .x11]

/-- The register holding working variable `k` (`a = 0, …, h = 7`) at the start of round `t`. -/
def var (t k : Nat) : Reg := work.getD ((k + 8 - t % 8) % 8) .x4

/-- Temporaries; `T0` holds `Wₜ` at the start of each round. -/
def T0 : Reg := .x12
def T1 : Reg := .x13
def T2 : Reg := .x14
def T3 : Reg := .x15

/-- The offset of `W[i mod 16]` in the scratch buffer. -/
def slot (i : Nat) : Nat := 4 * (i % 16)

/-- Leave `Wₜ` in `T0` and in its slot. The additions are in the order of the
specification. -/
def schedule (t : Nat) : List Instr :=
  if t < 16 then [
    .ldr .w T0 .x1 (4 * t),
    .rev32 T0 T0,
    .str .w T0 .x3 (slot t)]
  else [
    -- T0 := σ₁(Wₜ₋₂)
    .ldr .w T1 .x3 (slot (t + 14)),
    .ror .w T0 T1 17,
    .ror .w T2 T1 19,
    .logic .eor .w T0 T0 T2,
    .lsr .w T2 T1 10,
    .logic .eor .w T0 T0 T2,
    -- T0 := T0 + Wₜ₋₇
    .ldr .w T2 .x3 (slot (t + 9)),
    .add .w T0 T0 T2,
    -- T0 := T0 + σ₀(Wₜ₋₁₅)
    .ldr .w T1 .x3 (slot (t + 1)),
    .ror .w T2 T1 7,
    .ror .w T3 T1 18,
    .logic .eor .w T2 T2 T3,
    .lsr .w T3 T1 3,
    .logic .eor .w T2 T2 T3,
    .add .w T0 T0 T2,
    -- T0 := T0 + Wₜ₋₁₆
    .ldr .w T2 .x3 (slot t),
    .add .w T0 T0 T2,
    .str .w T0 .x3 (slot t)]

/-- Round `t`, with `Wₜ` in `T0`. The additions are in the order of the
specification. -/
def round (t : Nat) : List Instr :=
  let a := var t 0; let b := var t 1; let c := var t 2; let d := var t 3
  let e := var t 4; let f := var t 5; let g := var t 6; let h := var t 7
  [ -- h := h + Σ₁(e)
    .ror .w T1 e 6,
    .ror .w T2 e 11,
    .logic .eor .w T1 T1 T2,
    .ror .w T2 e 25,
    .logic .eor .w T1 T1 T2,
    .add .w h h T1,
    -- h := h + Ch(e, f, g), as ((f ⊕ g) ∧ e) ⊕ g
    .logic .eor .w T1 f g,
    .logic .and .w T1 T1 e,
    .logic .eor .w T1 T1 g,
    .add .w h h T1,
    -- h := h + Kₜ + Wₜ, which is T₁
    .movz .w T1 ((K t).extractLsb' 0 16) 0,
    .movk .w T1 ((K t).extractLsb' 16 16) 1,
    .add .w h h T1,
    .add .w h h T0,
    -- e' := d + T₁
    .add .w d d h,
    -- h := h + Σ₀(a)
    .ror .w T1 a 2,
    .ror .w T2 a 13,
    .logic .eor .w T1 T1 T2,
    .ror .w T2 a 22,
    .logic .eor .w T1 T1 T2,
    .add .w h h T1,
    -- h := h + Maj(a, b, c), as ((a ∨ b) ∧ c) ∨ (a ∧ b); now h = a' = T₁ + T₂
    .logic .orr .w T1 a b,
    .logic .and .w T1 T1 c,
    .logic .and .w T2 a b,
    .logic .orr .w T1 T1 T2,
    .add .w h h T1]

/-- Rounds `0 … n-1`. -/
def rounds : Nat → Prog isa
  | 0 => .block []
  | n + 1 => .seq (rounds n) (.block (schedule n ++ round n))

/-- Load the hash value (`64 % 8 = 0`, so the variables are in the same
registers after the 64 rounds). -/
def load : List Instr := (List.range 8).map fun k => .ldr .w (var 0 k) .x0 (4 * k)

/-- Add the hash value into the working variables (loading all of it before
storing any of it), and store the result. -/
def update : List Instr :=
  (List.range 4).map (fun k => .ldr .w ([T0, T1, T2, T3].getD k T0) .x0 (4 * k)) ++
  (List.range 4).map (fun k => .add .w (var 0 k) (var 0 k) ([T0, T1, T2, T3].getD k T0)) ++
  (List.range 4).map (fun k => .ldr .w ([T0, T1, T2, T3].getD k T0) .x0 (4 * (k + 4))) ++
  (List.range 4).map (fun k => .add .w (var 0 (k + 4)) (var 0 (k + 4)) ([T0, T1, T2, T3].getD k T0)) ++
  (List.range 8).map (fun k => .str .w (var 0 k) .x0 (4 * k))

/-- Advance to the next block and decrement the count. -/
def advance : List Instr := [.addImm .x .x1 .x1 64, .subImm .x .x2 .x2 1]

/-- One block. -/
def body : Prog isa := .seq (.block load) (.seq (rounds 64) (.block (update ++ advance)))

def compress : Prog isa :=
  .ite (.zero .x .x2) (.block []) (.loop body (.nonzero .x .x2))

end VG.Impl.Sha256.AArch64
