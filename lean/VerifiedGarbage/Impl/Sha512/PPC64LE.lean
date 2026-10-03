import VerifiedGarbage.Spec.Sha512
import VerifiedGarbage.TCB.PPC64LE.Isa

/-!
# SHA-512 compression function: PPC64LE implementation

`vg_sha512_compress(state = r3, blocks = r4, n = r5, scratch = r6)`.

The same structure as the SHA-256 implementation (`VG.Impl.Sha256.PPC64LE`),
on whole 64-bit registers:
* The working variables `a … h` live in `r7`–`r12`, `r14` and `r15`; the
  fully unrolled rounds rename them: in round `t`, variable `k` is in
  `var t k`.
* The message schedule is a 16-word window in `scratch[0..128)`. The words
  of a block are loaded big-endian with `ldbrx`, indexed by `r0`.
* `Kₜ` is built with `lis`, `ori`, `sldi`, `oris` and `ori` (`movImm64`).
* `r14`–`r19` are nonvolatile: they are saved in `scratch[128..176)` first
  and restored last.
* `r3`–`r6` (the pointers and the block count) are public; no address and
  no branch depends on anything else.
-/

namespace VG.Impl.Sha512.PPC64LE

open VG.PPC64LE
open VG.Spec.Sha512 (K)

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

/-- Save them in `scratch[128..176)`. -/
def save : List Instr := (List.range 6).flatMap fun i => [.store .d (saved i) .r6 (128 + 8 * i)]

/-- Restore them. -/
def restore : List Instr := (List.range 6).flatMap fun i => [.load .d (saved i) .r6 (128 + 8 * i)]

/-- The offset of `W[i mod 16]` in the scratch buffer. -/
def slot (i : Nat) : Nat := 8 * (i % 16)

/-- `d := v` for a 64-bit constant: the high word with `lis` and `ori`,
shifted up by `sldi`, then the low word with `oris` and `ori`. -/
def movImm64 (d : Reg) (v : BitVec 64) : List Instr :=
  [.lis d (v.extractLsb' 48 16), .ori d d (v.extractLsb' 32 16), .lsl d d 32,
   .oris d d (v.extractLsb' 16 16), .ori d d (v.extractLsb' 0 16)]

/-- Leave `Wₜ` in `T0` and in its slot. The additions are in the order of the
specification. -/
def schedule (t : Nat) : List Instr :=
  if t < 16 then [
    .li .r0 (8 * t),
    .loadRev .d T0 .r4 .r0,
    .store .d T0 .r6 (slot t)]
  else [
    -- T0 := σ₁(Wₜ₋₂)
    .load .d T1 .r6 (slot (t + 14)),
    .rotr .d T0 T1 19,
    .rotr .d T2 T1 61,
    .logic .xor T0 T0 T2,
    .lsr .d T2 T1 6,
    .logic .xor T0 T0 T2,
    -- T0 := T0 + Wₜ₋₇
    .load .d T2 .r6 (slot (t + 9)),
    .add T0 T0 T2,
    -- T0 := T0 + σ₀(Wₜ₋₁₅)
    .load .d T1 .r6 (slot (t + 1)),
    .rotr .d T2 T1 1,
    .rotr .d T3 T1 8,
    .logic .xor T2 T2 T3,
    .lsr .d T3 T1 7,
    .logic .xor T2 T2 T3,
    .add T0 T0 T2,
    -- T0 := T0 + Wₜ₋₁₆
    .load .d T2 .r6 (slot t),
    .add T0 T0 T2,
    .store .d T0 .r6 (slot t)]

/-- Round `t`, with `Wₜ` in `T0`. The additions are in the order of the
specification. -/
def round (t : Nat) : List Instr :=
  let a := var t 0; let b := var t 1; let c := var t 2; let d := var t 3
  let e := var t 4; let f := var t 5; let g := var t 6; let h := var t 7
  [ -- h := h + Σ₁(e)
    .rotr .d T1 e 14,
    .rotr .d T2 e 18,
    .logic .xor T1 T1 T2,
    .rotr .d T2 e 41,
    .logic .xor T1 T1 T2,
    .add h h T1,
    -- h := h + Ch(e, f, g), as ((f ⊕ g) ∧ e) ⊕ g
    .logic .xor T1 f g,
    .logic .and T1 T1 e,
    .logic .xor T1 T1 g,
    .add h h T1] ++
  -- h := h + Kₜ + Wₜ, which is T₁
  movImm64 T1 (K t) ++
  [ .add h h T1,
    .add h h T0,
    -- e' := d + T₁
    .add d d h,
    -- h := h + Σ₀(a)
    .rotr .d T1 a 28,
    .rotr .d T2 a 34,
    .logic .xor T1 T1 T2,
    .rotr .d T2 a 39,
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

/-- Load the hash value (`80 % 8 = 0`, so the variables are in the same
registers after the 80 rounds). -/
def load : List Instr := (List.range 8).map fun k => .load .d (var 0 k) .r3 (8 * k)

/-- Add the hash value into the working variables (loading all of it before
storing any of it), and store the result. -/
def update : List Instr :=
  (List.range 4).map (fun k => .load .d ([T0, T1, T2, T3].getD k T0) .r3 (8 * k)) ++
  (List.range 4).map (fun k => .add (var 0 k) (var 0 k) ([T0, T1, T2, T3].getD k T0)) ++
  (List.range 4).map (fun k => .load .d ([T0, T1, T2, T3].getD k T0) .r3 (8 * (k + 4))) ++
  (List.range 4).map (fun k => .add (var 0 (k + 4)) (var 0 (k + 4)) ([T0, T1, T2, T3].getD k T0)) ++
  (List.range 8).map (fun k => .store .d (var 0 k) .r3 (8 * k))

/-- Advance to the next block and decrement the count. -/
def advance : List Instr := [.addi .r4 .r4 128, .subi .r5 .r5 1]

/-- One block. -/
def body : Prog isa := .seq (.block load) (.seq (rounds 80) (.block (update ++ advance)))

/-- The blocks. -/
def blocks : Prog isa := .ite (.zero .d .r5) (.block []) (.loop body (.nonzero .d .r5))

def compress : Prog isa := .seq (.block save) (.seq blocks (.block restore))

end VG.Impl.Sha512.PPC64LE
