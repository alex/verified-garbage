import VerifiedGarbage.Spec.Sha512
import VerifiedGarbage.TCB.AArch64.Isa

/-!
# SHA-512 compression function: AArch64 implementation

`vg_sha512_compress(state = x0, blocks = x1, n = x2, scratch = x3)`.

The same structure as the SHA-256 implementation, on 64-bit registers:
* The working variables `a … h` live in `x4`–`x11`; the fully unrolled rounds
  rename them: in round `t`, variable `k` is in `var t k`.
* The message schedule is a 16-word window in `scratch[0..128)`.
* `Kₜ` is built with a `movz` and three `movk`s.
* Only caller-saved registers are used (`x0`–`x15`), so nothing is saved.
* `x0`–`x3` (the pointers and the block count) are public; no address and
  no branch depends on anything else.
-/

namespace VG.Impl.Sha512.AArch64

open VG.AArch64
open VG.Spec.Sha512 (K)

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
def slot (i : Nat) : Nat := 8 * (i % 16)

/-- `mov d, #v` for a 64-bit constant: a `movz` and three `movk`s. -/
def movImm64 (d : Reg) (v : BitVec 64) : List Instr :=
  [.movz .x d (v.extractLsb' 0 16) 0, .movk .x d (v.extractLsb' 16 16) 1,
   .movk .x d (v.extractLsb' 32 16) 2, .movk .x d (v.extractLsb' 48 16) 3]

/-- Leave `Wₜ` in `T0` and in its slot. The additions are in the order of the
specification. -/
def schedule (t : Nat) : List Instr :=
  if t < 16 then [
    .ldr .x T0 .x1 (8 * t),
    .rev T0 T0,
    .str .x T0 .x3 (slot t)]
  else [
    -- T0 := σ₁(Wₜ₋₂)
    .ldr .x T1 .x3 (slot (t + 14)),
    .ror .x T0 T1 19,
    .ror .x T2 T1 61,
    .logic .eor .x T0 T0 T2,
    .lsr .x T2 T1 6,
    .logic .eor .x T0 T0 T2,
    -- T0 := T0 + Wₜ₋₇
    .ldr .x T2 .x3 (slot (t + 9)),
    .add .x T0 T0 T2,
    -- T0 := T0 + σ₀(Wₜ₋₁₅)
    .ldr .x T1 .x3 (slot (t + 1)),
    .ror .x T2 T1 1,
    .ror .x T3 T1 8,
    .logic .eor .x T2 T2 T3,
    .lsr .x T3 T1 7,
    .logic .eor .x T2 T2 T3,
    .add .x T0 T0 T2,
    -- T0 := T0 + Wₜ₋₁₆
    .ldr .x T2 .x3 (slot t),
    .add .x T0 T0 T2,
    .str .x T0 .x3 (slot t)]

/-- Round `t`, with `Wₜ` in `T0`. The additions are in the order of the
specification. -/
def round (t : Nat) : List Instr :=
  let a := var t 0; let b := var t 1; let c := var t 2; let d := var t 3
  let e := var t 4; let f := var t 5; let g := var t 6; let h := var t 7
  [ -- h := h + Σ₁(e)
    .ror .x T1 e 14,
    .ror .x T2 e 18,
    .logic .eor .x T1 T1 T2,
    .ror .x T2 e 41,
    .logic .eor .x T1 T1 T2,
    .add .x h h T1,
    -- h := h + Ch(e, f, g), as ((f ⊕ g) ∧ e) ⊕ g
    .logic .eor .x T1 f g,
    .logic .and .x T1 T1 e,
    .logic .eor .x T1 T1 g,
    .add .x h h T1] ++
  -- h := h + Kₜ + Wₜ, which is T₁
  movImm64 T1 (K t) ++
  [ .add .x h h T1,
    .add .x h h T0,
    -- e' := d + T₁
    .add .x d d h,
    -- h := h + Σ₀(a)
    .ror .x T1 a 28,
    .ror .x T2 a 34,
    .logic .eor .x T1 T1 T2,
    .ror .x T2 a 39,
    .logic .eor .x T1 T1 T2,
    .add .x h h T1,
    -- h := h + Maj(a, b, c), as ((a ∨ b) ∧ c) ∨ (a ∧ b); now h = a' = T₁ + T₂
    .logic .orr .x T1 a b,
    .logic .and .x T1 T1 c,
    .logic .and .x T2 a b,
    .logic .orr .x T1 T1 T2,
    .add .x h h T1]

/-- Rounds `0 … n-1`. -/
def rounds : Nat → Prog isa
  | 0 => .block []
  | n + 1 => .seq (rounds n) (.block (schedule n ++ round n))

/-- Load the hash value (`80 % 8 = 0`, so the variables are in the same
registers after the 80 rounds). -/
def load : List Instr := (List.range 8).map fun k => .ldr .x (var 0 k) .x0 (8 * k)

/-- Add the hash value into the working variables (loading all of it before
storing any of it), and store the result. -/
def update : List Instr :=
  (List.range 4).map (fun k => .ldr .x ([T0, T1, T2, T3].getD k T0) .x0 (8 * k)) ++
  (List.range 4).map (fun k => .add .x (var 0 k) (var 0 k) ([T0, T1, T2, T3].getD k T0)) ++
  (List.range 4).map (fun k => .ldr .x ([T0, T1, T2, T3].getD k T0) .x0 (8 * (k + 4))) ++
  (List.range 4).map (fun k => .add .x (var 0 (k + 4)) (var 0 (k + 4)) ([T0, T1, T2, T3].getD k T0)) ++
  (List.range 8).map (fun k => .str .x (var 0 k) .x0 (8 * k))

/-- Advance to the next block and decrement the count. -/
def advance : List Instr := [.addImm .x .x1 .x1 128, .subImm .x .x2 .x2 1]

/-- One block. -/
def body : Prog isa := .seq (.block load) (.seq (rounds 80) (.block (update ++ advance)))

def compress : Prog isa :=
  .ite (.zero .x .x2) (.block []) (.loop body (.nonzero .x .x2))

end VG.Impl.Sha512.AArch64
