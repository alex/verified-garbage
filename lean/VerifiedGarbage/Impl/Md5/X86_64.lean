import VerifiedGarbage.Spec.Md5
import VerifiedGarbage.TCB.X86_64.Isa

/-!
# MD5 compression function: x86-64 implementation

`vg_md5_compress(state = rdi, blocks = rsi, n = rdx, scratch = rcx)`.

* The MD buffer `A, B, C, D` lives in the low 32 bits of four registers,
  loaded once before the first block and kept there between blocks.
  Rather than moving the words at the end of every operation, the fully
  unrolled operations rename them: in operation `t`, word `k` of the
  specification's `(a, b, c, d)` is in `var t k`.
* Each word `X[k]` is added straight from the block (a little-endian 32-bit
  load), so there is no message schedule to keep.
* Each operation is scheduled for latency: `b` is the word the previous
  operation computed, so everything that does not depend on it is computed
  first. `a + X[k] + T[t+1]` is added before the auxiliary function, and so
  are the terms of the auxiliary functions that do not depend on `b`: `G`
  is added as `(¬d ∧ c) + (d ∧ b)` (the two terms have no bit in common),
  and `F` and `H` start with `c ⊕ d`. On the path from one operation's `b`
  to the next's are two instructions of `F` and `I` and one of `G` and
  `H`, then the addition into `a`, the rotation and the addition of `b`.
* Only caller-saved registers are used (`rax, r8–r11` and the argument
  registers), so nothing is saved, and `scratch` is not used.
* `rdi, rsi, rdx, rcx` (the pointers and the block count) are public; no
  address and no branch depends on anything else.
-/

namespace VG.Impl.Md5.X86_64

open VG.X86_64
open VG.Spec.Md5 (ks ss Ts)

/-- The registers holding the MD buffer. -/
def work : List Reg := [.rax, .r8, .r9, .r10]

/-- The register holding word `k` (`a = 0, …, d = 3`) at the start of operation `t`. -/
def var (t k : Nat) : Reg := work.getD ((k + 4 - t % 4) % 4) .rax

/-- The temporary, which holds the auxiliary function's value. -/
def T0 : Reg := .r11

def at_ (b : Reg) (d : Nat) : MemOp := { base := b, disp := d }

/-- `a := a + fn(b, c, d)`, the auxiliary function of round `r`, using `T0`:
`F = ((c ⊕ d) ∧ b) ⊕ d`, `G = (¬d ∧ c) + (d ∧ b)`, `H = (c ⊕ d) ⊕ b` and
`I = (¬d ∨ b) ⊕ c`, each with the instructions not depending on `b` first. -/
def fn (r : Nat) (a b c d : Reg) : List Instr :=
  match r with
  | 0 => [.mov32 T0 (.reg c), .alu32 .xor T0 (.reg d), .alu32 .and T0 (.reg b), .alu32 .xor T0 (.reg d),
      .alu32 .add a (.reg T0)]
  | 1 => [.mov32 T0 (.reg d), .alu32 .xor T0 (.imm 0xffffffff), .alu32 .and T0 (.reg c),
      .alu32 .add a (.reg T0), .mov32 T0 (.reg d), .alu32 .and T0 (.reg b), .alu32 .add a (.reg T0)]
  | 2 => [.mov32 T0 (.reg c), .alu32 .xor T0 (.reg d), .alu32 .xor T0 (.reg b), .alu32 .add a (.reg T0)]
  | _ => [.mov32 T0 (.reg d), .alu32 .xor T0 (.imm 0xffffffff), .alu32 .or T0 (.reg b),
      .alu32 .xor T0 (.reg c), .alu32 .add a (.reg T0)]

/-- The rotation amount `s` of operation `t`. -/
def rot (t : Nat) : Nat := (ss.getD (t / 16) []).getD (t % 4) 0

/-- Operation `t`: `a := b + ((a + X[k] + T[t+1] + fn(b,c,d)) <<< s)`, the
rotation as a right rotation by `32 - s`. -/
def step (t : Nat) : List Instr :=
  let a := var t 0; let b := var t 1; let c := var t 2; let d := var t 3
  [.alu32 .add a (.mem (at_ .rsi (4 * ks.getD t 0))), .alu32 .add a (.imm (Ts.getD t 0))] ++
  fn (t / 16) a b c d ++
  [.shift32 .ror a (32 - rot t), .alu32 .add a (.reg b)]

/-- Operations `0 … n-1`. -/
def steps : Nat → Prog isa
  | 0 => .block []
  | n + 1 => .seq (steps n) (.block (step n))

/-- Load the MD buffer (`64 % 4 = 0`, so the words are in the same registers
after the 64 operations). -/
def load : List Instr := (List.range 4).map fun k => .mov32 (var 0 k) (.mem (at_ .rdi (4 * k)))

/-- Add the words into the MD buffer, which they then hold for the next block. -/
def update : List Instr :=
  (List.range 4).map (fun k => .alu32 .add (var 0 k) (.mem (at_ .rdi (4 * k)))) ++
  (List.range 4).map (fun k => .store32 (at_ .rdi (4 * k)) (var 0 k))

/-- Advance to the next block and decrement the count (setting ZF when it hits 0). -/
def advance : List Instr := [.alu .add .rsi (.imm 64), .alu .sub .rdx (.imm 1)]

/-- One block. -/
def body : Prog isa := .seq (steps 64) (.block (update ++ advance))

def compress : Prog isa :=
  .seq (.block [.alu .test .rdx (.reg .rdx)]) (.ite .e (.block []) (.seq (.block load) (.loop body .ne)))

end VG.Impl.Md5.X86_64
