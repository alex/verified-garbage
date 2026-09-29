import VerifiedGarbage.Spec.Sha1
import VerifiedGarbage.TCB.Arm.Isa

/-!
# SHA-1 compression function: ARMv7 implementation

`vg_sha1_compress(state = r0, blocks = r1, n = r2, scratch = r3)`.

The same structure as the AArch64 implementation, with the temporaries of
the ARMv7 SHA-256 implementation:
* The working variables `a … e` live in `r4`–`r8`; the fully unrolled rounds
  rename them: in round `t`, variable `k` is in `var t k`. The temporaries
  are `r12` and `lr`.
* The message schedule is a 16-word window in `scratch[0..64)`; each round
  reads `Wₜ` from it.
* The callee-saved registers `r4`–`r11` and `lr` are saved in
  `scratch[64..100)` and restored on exit (`r9`–`r11` are not written, but
  restoring them too keeps the proof uniform with SHA-256's).
* `r0`–`r3` (the pointers and the block count) are public; no address and no
  branch depends on anything else.
-/

namespace VG.Impl.Sha1.Arm

open VG.Arm
open VG.Spec.Sha1 (K)

/-- The registers holding the working variables. -/
def work : List Reg := [.r4, .r5, .r6, .r7, .r8]

/-- The register holding working variable `k` (`a = 0, …, e = 4`) at the start of round `t`. -/
def var (t k : Nat) : Reg := work.getD ((k + 5 - t % 5) % 5) .r4

/-- Temporaries. -/
def T1 : Reg := .r12
def T2 : Reg := .lr

/-- The offset of `W[i mod 16]` in the scratch buffer. -/
def slot (i : Nat) : Nat := 4 * (i % 16)

/-- Store `Wₜ` in its slot. The operations are in the order of the
specification; `ROTL¹` is a rotation right by 31. -/
def schedule (t : Nat) : List Instr :=
  if t < 16 then [
    .ldr T1 .r1 (4 * t),
    .rev T1 T1,
    .str T1 .r3 (slot t)]
  else [
    -- Wₜ₋₃ ⊕ Wₜ₋₈ ⊕ Wₜ₋₁₄ ⊕ Wₜ₋₁₆
    .ldr T1 .r3 (slot (t + 13)),
    .ldr T2 .r3 (slot (t + 8)),
    .dp .eor T1 T1 (.reg T2),
    .ldr T2 .r3 (slot (t + 2)),
    .dp .eor T1 T1 (.reg T2),
    .ldr T2 .r3 (slot t),
    .dp .eor T1 T1 (.reg T2),
    .mov T1 (.shifted T1 .ror 31),
    .str T1 .r3 (slot t)]

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
    [.dp .eor T1 c (.reg d), .dp .and T1 T1 (.reg b), .dp .eor T1 T1 (.reg d)]
  | .parity => [.dp .eor T1 b (.reg c), .dp .eor T1 T1 (.reg d)]
  | .maj => -- `Maj(b, c, d)`, as `((b ∨ c) ∧ d) ∨ (b ∧ c)`
    [.dp .orr T1 b (.reg c), .dp .and T1 T1 (.reg d), .dp .and T2 b (.reg c),
      .dp .orr T1 T1 (.reg T2)]

/-- The rest of round `t`, with `f(b, c, d)` in `T1`:
`T = ROTL⁵(a) + f + e + Kₜ + Wₜ`, with the additions in the order of the
specification and `Wₜ` read from its slot, goes into `e`'s register (the new
`a`), and `b` becomes `ROTL³⁰(b)`. `ROTLⁿ` is a rotation right by `32 - n`. -/
def sum (t : Nat) (a b e : Reg) : List Instr := [
  .mov T2 (.shifted a .ror 27),
  .dp .add T2 T2 (.reg T1),
  .dp .add T2 T2 (.reg e),
  .movw T1 ((K t).extractLsb' 0 16),
  .movt T1 ((K t).extractLsb' 16 16),
  .dp .add T2 T2 (.reg T1),
  .ldr T1 .r3 (slot t),
  .dp .add e T2 (.reg T1),
  .mov b (.shifted b .ror 2)]

/-- Round `t`, reading `Wₜ` from its slot. -/
def round (t : Nat) : List Instr :=
  fcode (fn t) (var t 1) (var t 2) (var t 3) ++ sum t (var t 0) (var t 1) (var t 4)

/-- Rounds `0 … n-1`. -/
def rounds : Nat → Prog isa
  | 0 => .block []
  | n + 1 => .seq (rounds n) (.block (schedule n ++ round n))

/-- The callee-saved registers, and where they are saved. -/
def saved : List (Reg × Nat) :=
  [(.r4, 64), (.r5, 68), (.r6, 72), (.r7, 76), (.r8, 80), (.r9, 84), (.r10, 88), (.r11, 92),
   (.lr, 96)]

def save : List Instr := saved.map fun (r, d) => .str r .r3 d
def restore : List Instr := saved.map fun (r, d) => .ldr r .r3 d

/-- Load the hash value (`80 % 5 = 0`, so the variables are in the same
registers after the 80 rounds). -/
def load : List Instr := (List.range 5).map fun k => .ldr (var 0 k) .r0 (4 * k)

/-- Add the hash value into the working variables and store the result. -/
def update : List Instr :=
  (List.range 5).flatMap fun k => [
    .ldr T1 .r0 (4 * k),
    .dp .add (var 0 k) (var 0 k) (.reg T1),
    .str (var 0 k) .r0 (4 * k)]

/-- Advance to the next block and decrement the count (setting Z when it hits 0). -/
def advance : List Instr := [.dp .add .r1 .r1 (.imm 64), .subs .r2 .r2 (.imm 1)]

/-- One block. -/
def body : Prog isa := .seq (.block load) (.seq (rounds 80) (.block (update ++ advance)))

def compress : Prog isa :=
  .seq (.block (save ++ [.cmp .r2 (.imm 0)]))
    (.seq (.ite .eq (.block []) (.loop body .ne)) (.block restore))

end VG.Impl.Sha1.Arm
