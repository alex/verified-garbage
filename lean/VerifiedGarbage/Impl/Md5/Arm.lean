import VerifiedGarbage.Spec.Md5
import VerifiedGarbage.TCB.Arm.Isa

/-!
# MD5 compression function: ARMv7 implementation

`vg_md5_compress(state = r0, blocks = r1, n = r2, scratch = r3)`.

The same structure as the AArch64 implementation:
* The MD buffer `A, B, C, D` lives in `r4`–`r7`; the fully unrolled
  operations rename them: in operation `t`, word `k` of the specification's
  `(a, b, c, d)` is in `var t k`.
* Each word `X[k]` is loaded from the block (a little-endian 32-bit load)
  when it is added, so there is no message schedule to keep.
* The model has no `mvn`/`bic`, so `¬d` is `d ⊕ 0xffffffff`, with the
  constant in `r8`, set at the start of each block.
* The rotation and the final addition are one instruction,
  `add a, b, a, ror #(32 - s)`.
* `r4`–`r9` are saved in `scratch[0..24)` and restored on exit; `r0` and
  `r3` are never written, and neither are `r10`, `r11` and `lr`.
* `r0`–`r3` (the pointers and the block count) are public; no address and
  no branch depends on anything else.
-/

namespace VG.Impl.Md5.Arm

open VG.Arm
open VG.Spec.Md5 (ks ss Ts)

/-- The registers holding the MD buffer. -/
def work : List Reg := [.r4, .r5, .r6, .r7]

/-- The register holding word `k` (`a = 0, …, d = 3`) at the start of operation `t`. -/
def var (t k : Nat) : Reg := work.getD ((k + 4 - t % 4) % 4) .r4

/-- Temporaries: `T0` holds the auxiliary function's value, `T1` the word
`X[k]` and then the constant `T[t+1]`. -/
def T0 : Reg := .r12
def T1 : Reg := .r9

/-- The register holding `0xffffffff`. -/
def Ones : Reg := .r8

/-- `T0 := fn(b, c, d)`, the auxiliary function of round `r`, as
`F = ((c ⊕ d) ∧ b) ⊕ d`, `G = ((b ⊕ c) ∧ d) ⊕ c`, `H = (b ⊕ c) ⊕ d` and
`I = ((d ⊕ 0xffffffff) ∨ b) ⊕ c`. -/
def fn (r : Nat) (b c d : Reg) : List Instr :=
  match r with
  | 0 => [.dp .eor T0 c (.reg d), .dp .and T0 T0 (.reg b), .dp .eor T0 T0 (.reg d)]
  | 1 => [.dp .eor T0 b (.reg c), .dp .and T0 T0 (.reg d), .dp .eor T0 T0 (.reg c)]
  | 2 => [.dp .eor T0 b (.reg c), .dp .eor T0 T0 (.reg d)]
  | _ => [.dp .eor T0 d (.reg Ones), .dp .orr T0 T0 (.reg b), .dp .eor T0 T0 (.reg c)]

/-- The rotation amount `s` of operation `t`. -/
def rot (t : Nat) : Nat := (ss.getD (t / 16) []).getD (t % 4) 0

/-- Operation `t`: `a := b + ((a + fn(b,c,d) + X[k] + T[t+1]) <<< s)`, the
rotation as a right rotation by `32 - s`. The additions are in the order of
the specification. -/
def step (t : Nat) : List Instr :=
  let a := var t 0; let b := var t 1; let c := var t 2; let d := var t 3
  fn (t / 16) b c d ++ [
    .dp .add a a (.reg T0),
    .ldr T1 .r1 (4 * ks.getD t 0),
    .dp .add a a (.reg T1),
    .movw T1 ((Ts.getD t 0).extractLsb' 0 16),
    .movt T1 ((Ts.getD t 0).extractLsb' 16 16),
    .dp .add a a (.reg T1),
    .dp .add a b (.shifted a .ror (32 - rot t))]

/-- Operations `0 … n-1`. -/
def steps : Nat → Prog isa
  | 0 => .block []
  | n + 1 => .seq (steps n) (.block (step n))

/-- `0xffffffff`. -/
def ones : BitVec 32 := 0xffffffff

/-- The callee-saved registers we use, and where they are saved. -/
def saved : List (Reg × Nat) := [(.r4, 0), (.r5, 4), (.r6, 8), (.r7, 12), (.r8, 16), (.r9, 20)]

def save : List Instr := saved.map fun (r, d) => .str r .r3 d
def restore : List Instr := saved.map fun (r, d) => .ldr r .r3 d

/-- Load the MD buffer (`64 % 4 = 0`, so the words are in the same registers
after the 64 operations), and set `Ones`. -/
def load : List Instr :=
  (List.range 4).map (fun k => .ldr (var 0 k) .r0 (4 * k)) ++
  [.movw Ones (ones.extractLsb' 0 16), .movt Ones (ones.extractLsb' 16 16)]

/-- Add the MD buffer into the words and store the result. -/
def update : List Instr :=
  (List.range 4).flatMap fun k => [
    .ldr T0 .r0 (4 * k),
    .dp .add (var 0 k) (var 0 k) (.reg T0),
    .str (var 0 k) .r0 (4 * k)]

/-- Advance to the next block and decrement the count (setting Z when it hits 0). -/
def advance : List Instr := [.dp .add .r1 .r1 (.imm 64), .subs .r2 .r2 (.imm 1)]

/-- One block. -/
def body : Prog isa := .seq (.block load) (.seq (steps 64) (.block (update ++ advance)))

def compress : Prog isa :=
  .seq (.block (save ++ [.cmp .r2 (.imm 0)]))
    (.seq (.ite .eq (.block []) (.loop body .ne)) (.block restore))

end VG.Impl.Md5.Arm
