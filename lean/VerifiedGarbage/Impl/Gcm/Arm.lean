import VerifiedGarbage.TCB.Arm.Isa

/-!
# GHASH: ARMv7 implementation

`vg_ghash(h = r0, y = r1, data = r2, n = r3, scratch = [sp])`.

For each of the `n` blocks `X` at `data`, `Y := (Y ⊕ X) • H`, where `•` is
SP 800-38D Algorithm 1 bit by bit, as `Spec.Gcm.mul` defines it:

* The callee-saved registers `r4`–`r11` and `lr` are saved in the first 36
  bytes of the scratch buffer (whose base is kept in `r12`), and `h`, `data`
  and `n` in the next 12 (`data` and `n` advance there); `y` stays in `r1`.
* `Y ⊕ X` is written over `Y` at `y`, 4 bytes at a time, and read back a
  byte at a time (at `lr`), most significant first. Each byte is inverted
  and shifted to the top of `x` (`r10`); each step turns the top bit into
  the mask `m = (x >> 31) − 1`, which is all ones exactly when the bit
  `xᵢ` is set, and shifts `x` left by one bit.
* A 128-bit value is four big-endian words, the most significant first:
  `Z` in `r2`–`r5` and `V` in `r6`–`r9` (loaded with `ldr` and `rev`).
* `Z` accumulates `V & m`, so `Z := Z ⊕ V` exactly when `xᵢ = 1`.
* `V` is shifted right by one bit, and the reduction constant `R` (its top
  byte `0xE1`, an immediate) is XORed into it under the mask
  `(LSB₁(V) ⊕ 1) − 1`.
* The 128 steps are a loop of 8 steps (a byte) per iteration, until `lr`
  is 16 bytes past `y`. `Y` is written back to `y` after every block.
* The pointers and the block count are public, and so is everything
  computed from them; no address and no branch depends on anything else.
-/

namespace VG.Impl.Gcm.Arm

open VG.Arm

/-- The scratch buffer's base. -/
def SB : Reg := .r12
/-- The block `Y`. -/
def YP : Reg := .r1
/-- The product so far, `Z`, word `k` (the most significant first). -/
def Z : Nat → Reg
  | 0 => .r2 | 1 => .r3 | 2 => .r4 | _ => .r5
/-- `V`. -/
def V : Nat → Reg
  | 0 => .r6 | 1 => .r7 | 2 => .r8 | _ => .r9
/-- The inverted bits of `Y ⊕ X` still to use, at the top. -/
def XR : Reg := .r10
/-- The masks. -/
def M : Reg := .r11
/-- A temporary. -/
def T : Reg := .r0
/-- The next byte of `Y ⊕ X`. -/
def XP : Reg := .lr

/-- The callee-saved registers, and their slots. -/
def savedRegs : List (Reg × Nat) :=
  [(.r4, 0), (.r5, 1), (.r6, 2), (.r7, 3), (.r8, 4), (.r9, 5), (.r10, 6), (.r11, 7), (.lr, 8)]

/-- The slots of `h`, `data` and `n`. -/
def hSlot : Nat := 9
def dSlot : Nat := 10
def nSlot : Nat := 11

/-- One step `i` of Algorithm 1. -/
def step : List Instr := [
  -- M := −xᵢ, and x := x << 1
  .mov T (.shifted XR .lsr 31),
  .dp .sub M T (.imm 1),
  .mov XR (.shifted XR .lsl 1),
  -- Z := Z ⊕ (V ∧ M)
  .dp .and T (V 0) (.reg M), .dp .eor (Z 0) (Z 0) (.reg T),
  .dp .and T (V 1) (.reg M), .dp .eor (Z 1) (Z 1) (.reg T),
  .dp .and T (V 2) (.reg M), .dp .eor (Z 2) (Z 2) (.reg T),
  .dp .and T (V 3) (.reg M), .dp .eor (Z 3) (Z 3) (.reg T),
  -- M := −LSB₁(V)
  .dp .and T (V 3) (.imm 1),
  .dp .eor T T (.imm 1),
  .dp .sub M T (.imm 1),
  -- V := (V >> 1) ⊕ (R ∧ M)
  .mov (V 3) (.shifted (V 3) .lsr 1), .dp .eor (V 3) (V 3) (.shifted (V 2) .lsl 31),
  .mov (V 2) (.shifted (V 2) .lsr 1), .dp .eor (V 2) (V 2) (.shifted (V 1) .lsl 31),
  .mov (V 1) (.shifted (V 1) .lsr 1), .dp .eor (V 1) (V 1) (.shifted (V 0) .lsl 31),
  .mov (V 0) (.shifted (V 0) .lsr 1),
  .dp .and M M (.imm 0xE1000000),
  .dp .eor (V 0) (V 0) (.reg M)]

/-- The next byte, inverted, at the top of `x`; the 8 steps; and whether
the block is done. -/
def steps : List Instr :=
  [.ldrb XR XP 0, .dp .eor XR XR (.imm 0xFF), .mov XR (.shifted XR .lsl 24),
   .dp .add XP XP (.imm 1)] ++
  (List.range 8).flatMap (fun _ => step) ++ [.dp .sub T XP (.reg YP), .cmp T (.imm 16)]

/-- `Y := Y ⊕ X`, `V := H`, `Z := 0`, and `x` at the first byte. -/
def load : List Instr :=
  [.ldr M SB (4 * dSlot)] ++
  ((List.range 4).flatMap fun k =>
    [.ldr XR YP (4 * k), .ldr T M (4 * k), .dp .eor XR XR (.reg T), .str XR YP (4 * k)]) ++
  [.ldr M SB (4 * hSlot)] ++
  ((List.range 4).flatMap fun k => [.ldr (V k) M (4 * k), .rev (V k) (V k)]) ++
  ((List.range 4).map fun k => .mov (Z k) (.imm 0)) ++
  [.mov XP (.reg YP)]

/-- Store `Z` as the new `Y`, advance to the next block and count it. -/
def store : List Instr :=
  ((List.range 4).flatMap fun k => [.rev (Z k) (Z k), .str (Z k) YP (4 * k)]) ++
  [.ldr T SB (4 * dSlot), .dp .add T T (.imm 16), .str T SB (4 * dSlot),
   .ldr T SB (4 * nSlot), .subs T T (.imm 1), .str T SB (4 * nSlot)]

/-- One block. -/
def body : Prog isa := .seq (.block load) (.seq (.loop (.block steps) .ne) (.block store))

def ghash : Prog isa :=
  .seq (.block ([.ldrSp SB 0] ++ savedRegs.map (fun (r, k) => .str r SB (4 * k)) ++
      [.str .r0 SB (4 * hSlot), .str .r2 SB (4 * dSlot), .str .r3 SB (4 * nSlot),
       .cmp .r3 (.imm 0)]))
    (.seq (.ite .eq (.block []) (.loop body .ne))
      (.block (savedRegs.map fun (r, k) => .ldr r SB (4 * k))))

end VG.Impl.Gcm.Arm
