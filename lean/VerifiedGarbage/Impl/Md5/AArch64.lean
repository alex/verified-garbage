import VerifiedGarbage.Spec.Md5
import VerifiedGarbage.TCB.AArch64.Isa

/-!
# MD5 compression function: AArch64 implementation

`vg_md5_compress(state = x0, blocks = x1, n = x2, scratch = x3)`.

The same structure as the x86-64 implementation:
* The MD buffer `A, B, C, D` lives in `w4`–`w7`; the fully unrolled
  operations rename them: in operation `t`, word `k` of the specification's
  `(a, b, c, d)` is in `var t k`.
* Each word `X[k]` is loaded from the block (a little-endian 32-bit load)
  when it is added, so there is no message schedule to keep.
* The model has no `bic`/`orn`/`mvn`, so `¬d` is `d ⊕ 0xffffffff`, with the
  constant in `w14`, set at the start of each block.
* Only caller-saved registers are used (`x0`–`x15`), so nothing is saved,
  and `scratch` is not used.
* `x0`–`x3` (the pointers and the block count) are public; no address and
  no branch depends on anything else.
-/

namespace VG.Impl.Md5.AArch64

open VG.AArch64
open VG.Spec.Md5 (ks ss Ts)

/-- The registers holding the MD buffer. -/
def work : List Reg := [.x4, .x5, .x6, .x7]

/-- The register holding word `k` (`a = 0, …, d = 3`) at the start of operation `t`. -/
def var (t k : Nat) : Reg := work.getD ((k + 4 - t % 4) % 4) .x4

/-- Temporaries: `T0` holds the auxiliary function's value, `T1` the word
`X[k]` and then the constant `T[t+1]`. -/
def T0 : Reg := .x12
def T1 : Reg := .x13

/-- The register holding `0xffffffff`. -/
def Ones : Reg := .x14

/-- `T0 := fn(b, c, d)`, the auxiliary function of round `r`, as
`F = ((c ⊕ d) ∧ b) ⊕ d`, `G = ((b ⊕ c) ∧ d) ⊕ c`, `H = (b ⊕ c) ⊕ d` and
`I = ((d ⊕ 0xffffffff) ∨ b) ⊕ c`. -/
def fn (r : Nat) (b c d : Reg) : List Instr :=
  match r with
  | 0 => [.logic .eor .w T0 c d, .logic .and .w T0 T0 b, .logic .eor .w T0 T0 d]
  | 1 => [.logic .eor .w T0 b c, .logic .and .w T0 T0 d, .logic .eor .w T0 T0 c]
  | 2 => [.logic .eor .w T0 b c, .logic .eor .w T0 T0 d]
  | _ => [.logic .eor .w T0 d Ones, .logic .orr .w T0 T0 b, .logic .eor .w T0 T0 c]

/-- The rotation amount `s` of operation `t`. -/
def rot (t : Nat) : Nat := (ss.getD (t / 16) []).getD (t % 4) 0

/-- Operation `t`: `a := b + ((a + fn(b,c,d) + X[k] + T[t+1]) <<< s)`, the
rotation as a right rotation by `32 - s`. The additions are in the order of
the specification. -/
def step (t : Nat) : List Instr :=
  let a := var t 0; let b := var t 1; let c := var t 2; let d := var t 3
  fn (t / 16) b c d ++ [
    .add .w a a T0,
    .ldr .w T1 .x1 (4 * ks.getD t 0),
    .add .w a a T1,
    .movz .w T1 ((Ts.getD t 0).extractLsb' 0 16) 0,
    .movk .w T1 ((Ts.getD t 0).extractLsb' 16 16) 1,
    .add .w a a T1,
    .ror .w a a (32 - rot t),
    .add .w a a b]

/-- Operations `0 … n-1`. -/
def steps : Nat → Prog isa
  | 0 => .block []
  | n + 1 => .seq (steps n) (.block (step n))

/-- `0xffffffff`. -/
def ones : BitVec 32 := 0xffffffff

/-- Load the MD buffer (`64 % 4 = 0`, so the words are in the same registers
after the 64 operations), and set `Ones`. -/
def load : List Instr :=
  (List.range 4).map (fun k => .ldr .w (var 0 k) .x0 (4 * k)) ++
  [.movz .w Ones (ones.extractLsb' 0 16) 0, .movk .w Ones (ones.extractLsb' 16 16) 1]

/-- Add the words into the MD buffer (loading all of it before storing any
of it), and store the result. -/
def update : List Instr :=
  (List.range 4).map (fun k => .ldr .w ([T0, T1, .x14, .x15].getD k T0) .x0 (4 * k)) ++
  (List.range 4).map (fun k => .add .w (var 0 k) (var 0 k) ([T0, T1, .x14, .x15].getD k T0)) ++
  (List.range 4).map (fun k => .str .w (var 0 k) .x0 (4 * k))

/-- Advance to the next block and decrement the count. -/
def advance : List Instr := [.addImm .x .x1 .x1 64, .subImm .x .x2 .x2 1]

/-- One block. -/
def body : Prog isa := .seq (.block load) (.seq (steps 64) (.block (update ++ advance)))

def compress : Prog isa :=
  .ite (.zero .x .x2) (.block []) (.loop body (.nonzero .x .x2))

end VG.Impl.Md5.AArch64
