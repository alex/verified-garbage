import VerifiedGarbage.Spec.Sha1
import VerifiedGarbage.TCB.AArch64.Isa

/-!
# SHA-1 compression function: AArch64 implementation

`vg_sha1_compress(state = x0, blocks = x1, n = x2, scratch = x3)`.

The same structure as the x86-64 implementation:
* The working variables `a … e` live in `w4`–`w8`; the fully unrolled rounds
  rename them: in round `t`, variable `k` is in `var t k`.
* The message schedule is a 16-word window in `scratch[0..64)`.
* Only caller-saved registers are used (`x0`–`x15`), so nothing is saved.
* `x0`–`x3` (the pointers and the block count) are public; no address and
  no branch depends on anything else.
-/

namespace VG.Impl.Sha1.AArch64

open VG.AArch64
open VG.Spec.Sha1 (K)

/-- The registers holding the working variables. -/
def work : List Reg := [.x4, .x5, .x6, .x7, .x8]

/-- The register holding working variable `k` (`a = 0, …, e = 4`) at the start of round `t`. -/
def var (t k : Nat) : Reg := work.getD ((k + 5 - t % 5) % 5) .x4

/-- Temporaries; `T0` holds `Wₜ` at the start of each round. -/
def T0 : Reg := .x12
def T1 : Reg := .x13
def T2 : Reg := .x14

/-- The offset of `W[i mod 16]` in the scratch buffer. -/
def slot (i : Nat) : Nat := 4 * (i % 16)

/-- Leave `Wₜ` in `T0` and in its slot. The operations are in the order of
the specification; `ROTL¹` is a rotation right by 31. -/
def schedule (t : Nat) : List Instr :=
  if t < 16 then [
    .ldr .w T0 .x1 (4 * t),
    .rev32 T0 T0,
    .str .w T0 .x3 (slot t)]
  else [
    -- Wₜ₋₃ ⊕ Wₜ₋₈ ⊕ Wₜ₋₁₄ ⊕ Wₜ₋₁₆
    .ldr .w T0 .x3 (slot (t + 13)),
    .ldr .w T1 .x3 (slot (t + 8)),
    .logic .eor .w T0 T0 T1,
    .ldr .w T1 .x3 (slot (t + 2)),
    .logic .eor .w T0 T0 T1,
    .ldr .w T1 .x3 (slot t),
    .logic .eor .w T0 T0 T1,
    .ror .w T0 T0 31,
    .str .w T0 .x3 (slot t)]

/-- The logical functions of §4.1.1. -/
inductive Fn | ch | parity | maj
  deriving DecidableEq

/-- The function `fₜ` of round `t`. -/
def fn (t : Nat) : Fn :=
  if t < 20 then .ch else if t < 40 then .parity else if t < 60 then .maj else .parity

/-- `T1 := f(b, c, d)` (using `T2` as well for `Maj`). -/
def fcode (f : Fn) (b c d : Reg) : List Instr :=
  match f with
  | .ch => -- `Ch(b, c, d)`, as `((c ⊕ d) ∧ b) ⊕ d`
    [.logic .eor .w T1 c d, .logic .and .w T1 T1 b, .logic .eor .w T1 T1 d]
  | .parity => [.logic .eor .w T1 b c, .logic .eor .w T1 T1 d]
  | .maj => -- `Maj(b, c, d)`, as `((b ∨ c) ∧ d) ∨ (b ∧ c)`
    [.logic .orr .w T1 b c, .logic .and .w T1 T1 d, .logic .and .w T2 b c,
      .logic .orr .w T1 T1 T2]

/-- The rest of round `t`, with `f(b, c, d)` in `T1` and `Wₜ` in `T0`:
`T = ROTL⁵(a) + f + e + Kₜ + Wₜ`, with the additions in the order of the
specification, goes into `e`'s register (the new `a`), and `b` becomes
`ROTL³⁰(b)`. `ROTLⁿ` is a rotation right by `32 - n`. -/
def sum (t : Nat) (a b e : Reg) : List Instr := [
  .ror .w T2 a 27,
  .add .w T2 T2 T1,
  .add .w T2 T2 e,
  .movz .w T1 ((K t).extractLsb' 0 16) 0,
  .movk .w T1 ((K t).extractLsb' 16 16) 1,
  .add .w T2 T2 T1,
  .add .w e T2 T0,
  .ror .w b b 2]

/-- Round `t`, with `Wₜ` in `T0`. -/
def round (t : Nat) : List Instr :=
  fcode (fn t) (var t 1) (var t 2) (var t 3) ++ sum t (var t 0) (var t 1) (var t 4)

/-- Rounds `0 … n-1`. -/
def rounds : Nat → Prog isa
  | 0 => .block []
  | n + 1 => .seq (rounds n) (.block (schedule n ++ round n))

/-- Load the hash value (`80 % 5 = 0`, so the variables are in the same
registers after the 80 rounds). -/
def load : List Instr := (List.range 5).map fun k => .ldr .w (var 0 k) .x0 (4 * k)

/-- Temporaries for the hash value while adding it in. -/
def tmp : List Reg := [.x9, .x10, .x11, .x12, .x13]

/-- Add the hash value into the working variables (loading all of it before
storing any of it), and store the result. -/
def update : List Instr :=
  (List.range 5).map (fun k => .ldr .w (tmp.getD k .x9) .x0 (4 * k)) ++
  (List.range 5).map (fun k => .add .w (var 0 k) (var 0 k) (tmp.getD k .x9)) ++
  (List.range 5).map (fun k => .str .w (var 0 k) .x0 (4 * k))

/-- Advance to the next block and decrement the count. -/
def advance : List Instr := [.addImm .x .x1 .x1 64, .subImm .x .x2 .x2 1]

/-- One block. -/
def body : Prog isa := .seq (.block load) (.seq (rounds 80) (.block (update ++ advance)))

def compress : Prog isa :=
  .ite (.zero .x .x2) (.block []) (.loop body (.nonzero .x .x2))

end VG.Impl.Sha1.AArch64
