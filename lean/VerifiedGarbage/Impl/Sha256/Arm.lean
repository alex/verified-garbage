import VerifiedGarbage.Spec.Sha256
import VerifiedGarbage.TCB.Arm.Isa

/-!
# SHA-256 compression function: ARMv7 implementation

`vg_sha256_compress(state = r0, blocks = r1, n = r2, scratch = r3)`.

The same structure as the x86-64 implementation, with fewer registers:
* The working variables `a … h` live in `r4`–`r11`; the fully unrolled rounds
  rename them: in round `t`, variable `k` is in `var t k`. The temporaries
  are `r12` and `lr`.
* The message schedule is a 16-word window in `scratch[0..64)`; each round
  reads `Wₜ` from it. `scratch[64..68)` holds an intermediate sum of the
  schedule (there is no third temporary register).
* `r4`–`r11` and `lr` are saved in `scratch[68..104)` and restored on exit.
* `r0`–`r3` (the pointers and the block count) are public; no address and no
  branch depends on anything else.
-/

namespace VG.Impl.Sha256.Arm

open VG.Arm
open VG.Spec.Sha256 (K)

/-- The registers holding the working variables. -/
def work : List Reg := [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11]

/-- The register holding working variable `k` (`a = 0, …, h = 7`) at the start of round `t`. -/
def var (t k : Nat) : Reg := work.getD ((k + 8 - t % 8) % 8) .r4

/-- Temporaries. -/
def T1 : Reg := .r12
def T2 : Reg := .lr

/-- The offset of `W[i mod 16]` in the scratch buffer. -/
def slot (i : Nat) : Nat := 4 * (i % 16)

/-- The offset of the schedule's intermediate sum. -/
def tmp : Nat := 64

/-- Store `Wₜ` in its slot. The additions are in the order of the specification. -/
def schedule (t : Nat) : List Instr :=
  if t < 16 then [
    .ldr T1 .r1 (4 * t),
    .rev T1 T1,
    .str T1 .r3 (slot t)]
  else [
    -- T1 := σ₁(Wₜ₋₂) + Wₜ₋₇, saved in `tmp`
    .ldr T2 .r3 (slot (t + 14)),
    .mov T1 (.shifted T2 .ror 17),
    .dp .eor T1 T1 (.shifted T2 .ror 19),
    .dp .eor T1 T1 (.shifted T2 .lsr 10),
    .ldr T2 .r3 (slot (t + 9)),
    .dp .add T1 T1 (.reg T2),
    .str T1 .r3 tmp,
    -- T1 := σ₀(Wₜ₋₁₅)
    .ldr T2 .r3 (slot (t + 1)),
    .mov T1 (.shifted T2 .ror 7),
    .dp .eor T1 T1 (.shifted T2 .ror 18),
    .dp .eor T1 T1 (.shifted T2 .lsr 3),
    -- T1 := (σ₁(Wₜ₋₂) + Wₜ₋₇) + σ₀(Wₜ₋₁₅) + Wₜ₋₁₆
    .ldr T2 .r3 tmp,
    .dp .add T1 T2 (.reg T1),
    .ldr T2 .r3 (slot t),
    .dp .add T1 T1 (.reg T2),
    .str T1 .r3 (slot t)]

/-- Round `t`, reading `Wₜ` from its slot. The additions are in the order of
the specification. -/
def round (t : Nat) : List Instr :=
  let a := var t 0; let b := var t 1; let c := var t 2; let d := var t 3
  let e := var t 4; let f := var t 5; let g := var t 6; let h := var t 7
  [ -- h := h + Σ₁(e)
    .mov T1 (.shifted e .ror 6),
    .dp .eor T1 T1 (.shifted e .ror 11),
    .dp .eor T1 T1 (.shifted e .ror 25),
    .dp .add h h (.reg T1),
    -- h := h + Ch(e, f, g), as ((f ⊕ g) ∧ e) ⊕ g
    .dp .eor T1 f (.reg g),
    .dp .and T1 T1 (.reg e),
    .dp .eor T1 T1 (.reg g),
    .dp .add h h (.reg T1),
    -- h := h + Kₜ + Wₜ, which is T₁
    .movw T1 ((K t).extractLsb' 0 16),
    .movt T1 ((K t).extractLsb' 16 16),
    .dp .add h h (.reg T1),
    .ldr T1 .r3 (slot t),
    .dp .add h h (.reg T1),
    -- e' := d + T₁
    .dp .add d d (.reg h),
    -- h := h + Σ₀(a)
    .mov T1 (.shifted a .ror 2),
    .dp .eor T1 T1 (.shifted a .ror 13),
    .dp .eor T1 T1 (.shifted a .ror 22),
    .dp .add h h (.reg T1),
    -- h := h + Maj(a, b, c), as ((a ∨ b) ∧ c) ∨ (a ∧ b); now h = a' = T₁ + T₂
    .dp .orr T1 a (.reg b),
    .dp .and T1 T1 (.reg c),
    .dp .and T2 a (.reg b),
    .dp .orr T1 T1 (.reg T2),
    .dp .add h h (.reg T1)]

/-- Rounds `0 … n-1`. -/
def rounds : Nat → Prog isa
  | 0 => .block []
  | n + 1 => .seq (rounds n) (.block (schedule n ++ round n))

/-- The callee-saved registers we use, and where they are saved. -/
def saved : List (Reg × Nat) :=
  [(.r4, 68), (.r5, 72), (.r6, 76), (.r7, 80), (.r8, 84), (.r9, 88), (.r10, 92), (.r11, 96),
   (.lr, 100)]

def save : List Instr := saved.map fun (r, d) => .str r .r3 d
def restore : List Instr := saved.map fun (r, d) => .ldr r .r3 d

/-- Load the hash value (`64 % 8 = 0`, so the variables are in the same
registers after the 64 rounds). -/
def load : List Instr := (List.range 8).map fun k => .ldr (var 0 k) .r0 (4 * k)

/-- Add the hash value into the working variables and store the result. -/
def update : List Instr :=
  (List.range 8).flatMap fun k => [
    .ldr T1 .r0 (4 * k),
    .dp .add (var 0 k) (var 0 k) (.reg T1),
    .str (var 0 k) .r0 (4 * k)]

/-- Advance to the next block and decrement the count (setting Z when it hits 0). -/
def advance : List Instr := [.dp .add .r1 .r1 (.imm 64), .subs .r2 .r2 (.imm 1)]

/-- One block. -/
def body : Prog isa := .seq (.block load) (.seq (rounds 64) (.block (update ++ advance)))

def compress : Prog isa :=
  .seq (.block (save ++ [.cmp .r2 (.imm 0)]))
    (.seq (.ite .eq (.block []) (.loop body .ne)) (.block restore))

end VG.Impl.Sha256.Arm
