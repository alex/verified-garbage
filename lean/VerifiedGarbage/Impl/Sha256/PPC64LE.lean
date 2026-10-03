import VerifiedGarbage.Spec.Sha256
import VerifiedGarbage.TCB.PPC64LE.Isa

/-!
# SHA-256 compression function: PPC64LE implementation

`vg_sha256_compress(state = r3, blocks = r4, n = r5, scratch = r6)`.

The same structure as the AArch64 implementation:
* The working variables `a … h` live in the low words of `r7`–`r12`, `r14`
  and `r15`; the fully unrolled rounds rename them: in round `t`, variable
  `k` is in `var t k`. The additions act on all 64 bits, so the high words
  hold carries, which the word rotates, shifts and stores ignore.
* The message schedule is a 16-word window in `scratch[0..64)`. The words
  of a block are loaded big-endian with `lwbrx`, indexed by `r0`.
* `r14`–`r19` are nonvolatile: they are saved in `scratch[64..112)` first and
  restored last.
* `r3`–`r6` (the pointers and the block count) are public; no address and
  no branch depends on anything else.
-/

namespace VG.Impl.Sha256.PPC64LE

open VG.PPC64LE
open VG.Spec.Sha256 (K)

/-- The registers holding the working variables. -/
def work : List Reg := [.r7, .r8, .r9, .r10, .r11, .r12, .r14, .r15]

/-- The register holding working variable `k` (`a = 0, …, h = 7`) at the start of round `t`. -/
def var (t k : Nat) : Reg := work.getD ((k + 8 - t % 8) % 8) .r7

/-- Temporaries; `T0` holds `Wₜ` at the start of each round. -/
def T0 : Reg := .r16
def T1 : Reg := .r17
def T2 : Reg := .r18
def T3 : Reg := .r19

/-- The nonvolatile registers used, in the order they are saved. -/
def saved (i : Nat) : Reg := [.r14, .r15, .r16, .r17, .r18, .r19].getD i .r14

/-- Save them in `scratch[64..112)`. -/
def save : List Instr := (List.range 6).flatMap fun i => [.store .d (saved i) .r6 (64 + 8 * i)]

/-- Restore them. -/
def restore : List Instr := (List.range 6).flatMap fun i => [.load .d (saved i) .r6 (64 + 8 * i)]

/-- The offset of `W[i mod 16]` in the scratch buffer. -/
def slot (i : Nat) : Nat := 4 * (i % 16)

/-- Leave `Wₜ` in the low word of `T0` and in its slot. The additions are in
the order of the specification. -/
def schedule (t : Nat) : List Instr :=
  if t < 16 then [
    .li .r0 (4 * t),
    .loadRev .w T0 .r4 .r0,
    .store .w T0 .r6 (slot t)]
  else [
    -- T0 := σ₁(Wₜ₋₂)
    .load .w T1 .r6 (slot (t + 14)),
    .rotr .w T0 T1 17,
    .rotr .w T2 T1 19,
    .logic .xor T0 T0 T2,
    .lsr .w T2 T1 10,
    .logic .xor T0 T0 T2,
    -- T0 := T0 + Wₜ₋₇
    .load .w T2 .r6 (slot (t + 9)),
    .add T0 T0 T2,
    -- T0 := T0 + σ₀(Wₜ₋₁₅)
    .load .w T1 .r6 (slot (t + 1)),
    .rotr .w T2 T1 7,
    .rotr .w T3 T1 18,
    .logic .xor T2 T2 T3,
    .lsr .w T3 T1 3,
    .logic .xor T2 T2 T3,
    .add T0 T0 T2,
    -- T0 := T0 + Wₜ₋₁₆
    .load .w T2 .r6 (slot t),
    .add T0 T0 T2,
    .store .w T0 .r6 (slot t)]

/-- Round `t`, with `Wₜ` in `T0`. The additions are in the order of the
specification. -/
def round (t : Nat) : List Instr :=
  let a := var t 0; let b := var t 1; let c := var t 2; let d := var t 3
  let e := var t 4; let f := var t 5; let g := var t 6; let h := var t 7
  [ -- h := h + Σ₁(e)
    .rotr .w T1 e 6,
    .rotr .w T2 e 11,
    .logic .xor T1 T1 T2,
    .rotr .w T2 e 25,
    .logic .xor T1 T1 T2,
    .add h h T1,
    -- h := h + Ch(e, f, g), as ((f ⊕ g) ∧ e) ⊕ g
    .logic .xor T1 f g,
    .logic .and T1 T1 e,
    .logic .xor T1 T1 g,
    .add h h T1,
    -- h := h + Kₜ + Wₜ, which is T₁
    .lis T1 ((K t).extractLsb' 16 16),
    .ori T1 T1 ((K t).extractLsb' 0 16),
    .add h h T1,
    .add h h T0,
    -- e' := d + T₁
    .add d d h,
    -- h := h + Σ₀(a)
    .rotr .w T1 a 2,
    .rotr .w T2 a 13,
    .logic .xor T1 T1 T2,
    .rotr .w T2 a 22,
    .logic .xor T1 T1 T2,
    .add h h T1,
    -- h := h + Maj(a, b, c), as ((a ∨ b) ∧ c) ∨ (a ∧ b); now h = a' = T₁ + T₂
    .logic .or T1 a b,
    .logic .and T1 T1 c,
    .logic .and T2 a b,
    .logic .or T1 T1 T2,
    .add h h T1]

/-- Rounds `0 … n-1`. -/
def rounds : Nat → Prog isa
  | 0 => .block []
  | n + 1 => .seq (rounds n) (.block (schedule n ++ round n))

/-- Load the hash value (`64 % 8 = 0`, so the variables are in the same
registers after the 64 rounds). -/
def load : List Instr := (List.range 8).map fun k => .load .w (var 0 k) .r3 (4 * k)

/-- Add the hash value into the working variables (loading all of it before
storing any of it), and store the result. -/
def update : List Instr :=
  (List.range 4).map (fun k => .load .w ([T0, T1, T2, T3].getD k T0) .r3 (4 * k)) ++
  (List.range 4).map (fun k => .add (var 0 k) (var 0 k) ([T0, T1, T2, T3].getD k T0)) ++
  (List.range 4).map (fun k => .load .w ([T0, T1, T2, T3].getD k T0) .r3 (4 * (k + 4))) ++
  (List.range 4).map (fun k => .add (var 0 (k + 4)) (var 0 (k + 4)) ([T0, T1, T2, T3].getD k T0)) ++
  (List.range 8).map (fun k => .store .w (var 0 k) .r3 (4 * k))

/-- Advance to the next block and decrement the count. -/
def advance : List Instr := [.addi .r4 .r4 64, .subi .r5 .r5 1]

/-- One block. -/
def body : Prog isa := .seq (.block load) (.seq (rounds 64) (.block (update ++ advance)))

/-- The blocks. -/
def blocks : Prog isa := .ite (.zero .d .r5) (.block []) (.loop body (.nonzero .d .r5))

def compress : Prog isa := .seq (.block save) (.seq blocks (.block restore))

end VG.Impl.Sha256.PPC64LE
