import VerifiedGarbage.TCB.AArch64.Isa

/-!
# GHASH: AArch64 implementation

`vg_ghash(h = x0, y = x1, data = x2, n = x3, scratch = x4)`.

For each of the `n` blocks `X` at `data`, `Y := (Y ⊕ X) • H`, where `•` is
SP 800-38D Algorithm 1 bit by bit, as `Spec.Gcm.mul` defines it:

* The blocks are big-endian: each 8-byte half is loaded with `ldr` and
  `rev`. A 128-bit value is kept in two registers, `hi` (the first eight
  bytes) and `lo`.
* `Y ⊕ X` is in `x5:x6`. Each step takes its most significant bit `xᵢ`
  (`lsr` by 63), turns it into the mask `m = 0 − xᵢ`, and shifts it left
  by one bit.
* `Z` (in `x7:x8`) accumulates `V & m`, so `Z := Z ⊕ V` exactly when
  `xᵢ = 1`.
* `V` (in `x9:x10`, starting at `H`) is shifted right by one bit, and the
  reduction constant `R` (the high half `0xE1 ‖ 0⁵⁶`, in `x13`) is XORed
  into it under the mask `0 − LSB₁(V)`.
* The 128 steps are a loop of `unroll` steps per iteration, counted down in
  `x14`; `x15` holds zero. `Y` is written back to `y` after every block.
* Only caller-saved registers are used, and the scratch buffer is not.
* `x0`–`x3` (the pointers and the block count) and `x14` are public; no
  address and no branch depends on anything else.
-/

namespace VG.Impl.Gcm.AArch64

open VG.AArch64

/-- `Y ⊕ X`, shifted left one bit per step. -/
def XH : Reg := .x5
def XL : Reg := .x6
/-- The product so far, `Z`. -/
def ZH : Reg := .x7
def ZL : Reg := .x8
/-- `V`. -/
def VH : Reg := .x9
def VL : Reg := .x10
/-- The masks `−xᵢ` and `−LSB₁(V)`. -/
def M : Reg := .x11
/-- A temporary. -/
def T : Reg := .x12
/-- The high half of `R`. -/
def RH : Reg := .x13
/-- The loop counter. -/
def CNT : Reg := .x14
/-- Zero. -/
def ZERO : Reg := .x15

/-- The high half of `R = 11100001 ‖ 0¹²⁰` (its low half is 0). -/
def rHigh : BitVec 64 := 0xE100000000000000

/-- Steps per iteration of the inner loop. -/
def unroll : Nat := 8

/-- One step `i` of Algorithm 1. -/
def step : List Instr := [
  -- M := −xᵢ, and X := X << 1
  .lsr .x T XH 63,
  .sub .x M ZERO T,
  .lsl .x XH XH 1,
  .lsr .x T XL 63,
  .logic .orr .x XH XH T,
  .lsl .x XL XL 1,
  -- Z := Z ⊕ (V ∧ M)
  .logic .and .x T VH M,
  .logic .eor .x ZH ZH T,
  .logic .and .x T VL M,
  .logic .eor .x ZL ZL T,
  -- M := −LSB₁(V)
  .lsl .x T VL 63,
  .lsr .x T T 63,
  .sub .x M ZERO T,
  -- V := (V >> 1) ⊕ (R ∧ M)
  .lsr .x VL VL 1,
  .lsl .x T VH 63,
  .logic .orr .x VL VL T,
  .lsr .x VH VH 1,
  .logic .and .x M M RH,
  .logic .eor .x VH VH M]

/-- `unroll` steps, then the count. -/
def steps : List Instr :=
  (List.range unroll).flatMap (fun _ => step) ++ [.subImm .x CNT CNT 1]

/-- Load `Y ⊕ X`, `V := H`, `Z := 0`, `R`, zero and the count. -/
def load : List Instr := [
  .ldr .x XH .x1 0, .rev XH XH,
  .ldr .x T .x2 0, .rev T T,
  .logic .eor .x XH XH T,
  .ldr .x XL .x1 8, .rev XL XL,
  .ldr .x T .x2 8, .rev T T,
  .logic .eor .x XL XL T,
  .ldr .x VH .x0 0, .rev VH VH,
  .ldr .x VL .x0 8, .rev VL VL,
  .movz .x ZH 0 0, .movz .x ZL 0 0,
  .movz .x RH 0xE100 3, .movz .x ZERO 0 0,
  .movz .x CNT (BitVec.ofNat 16 (128 / unroll)) 0]

/-- Store `Z` as the new `Y`, advance to the next block and count it. -/
def store : List Instr := [
  .rev ZH ZH, .str .x ZH .x1 0,
  .rev ZL ZL, .str .x ZL .x1 8,
  .addImm .x .x2 .x2 16, .subImm .x .x3 .x3 1]

/-- One block. -/
def body : Prog isa := .seq (.block load) (.seq (.loop (.block steps) (.nonzero .x CNT)) (.block store))

def ghash : Prog isa :=
  .ite (.zero .x .x3) (.block []) (.loop body (.nonzero .x .x3))

end VG.Impl.Gcm.AArch64
