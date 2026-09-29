import VerifiedGarbage.Spec.Md5
import VerifiedGarbage.TCB.X86.Isa

/-!
# MD5 compression function: x86 (32-bit) implementation

`vg_md5_compress(state, blocks, n, scratch)`, cdecl: the arguments are at
`[esp + 4]`, `[esp + 8]`, `[esp + 12]` and `[esp + 16]`.

The same structure as the x86-64 implementation:
* The MD buffer `A, B, C, D` lives in `eax`, `ebx`, `ecx`, `edx`; the fully
  unrolled operations rename them: in operation `t`, word `k` of the
  specification's `(a, b, c, d)` is in `var t k`.
* Each word `X[k]` is added straight from the block (a little-endian 32-bit
  load), so there is no message schedule to keep.
* `edi` holds the auxiliary function's value, `esi` points to the current
  block and `ebp` counts the blocks left; the state pointer is read from its
  argument slot into `edi` when the MD buffer is loaded and updated.
* `ebx`, `esi`, `edi` and `ebp` are saved in `scratch[0..16)` and restored
  on exit, with the scratch pointer read from its argument slot into `eax`.
* `esp` and the arguments (the pointers and the block count) are public; no
  address and no branch depends on anything else.
-/

namespace VG.Impl.Md5.X86

open VG.X86
open VG.Spec.Md5 (ks ss Ts)

/-- The registers holding the MD buffer. -/
def work : List Reg := [.eax, .ebx, .ecx, .edx]

/-- The register holding word `k` (`a = 0, …, d = 3`) at the start of operation `t`. -/
def var (t k : Nat) : Reg := work.getD ((k + 4 - t % 4) % 4) .eax

/-- The temporary, which holds the auxiliary function's value. -/
def T0 : Reg := .edi

def at_ (b : Reg) (d : Nat) : MemOp := { base := b, disp := d }

/-- `T0 := fn(b, c, d)`, the auxiliary function of round `r`, as
`F = ((c ⊕ d) ∧ b) ⊕ d`, `G = ((b ⊕ c) ∧ d) ⊕ c`, `H = (b ⊕ c) ⊕ d` and
`I = ((d ⊕ 0xffffffff) ∨ b) ⊕ c`. -/
def fn (r : Nat) (b c d : Reg) : List Instr :=
  match r with
  | 0 => [.mov T0 (.reg c), .alu .xor T0 (.reg d), .alu .and T0 (.reg b), .alu .xor T0 (.reg d)]
  | 1 => [.mov T0 (.reg b), .alu .xor T0 (.reg c), .alu .and T0 (.reg d), .alu .xor T0 (.reg c)]
  | 2 => [.mov T0 (.reg b), .alu .xor T0 (.reg c), .alu .xor T0 (.reg d)]
  | _ => [.mov T0 (.reg d), .alu .xor T0 (.imm 0xffffffff), .alu .or T0 (.reg b), .alu .xor T0 (.reg c)]

/-- The rotation amount `s` of operation `t`. -/
def rot (t : Nat) : Nat := (ss.getD (t / 16) []).getD (t % 4) 0

/-- Operation `t`: `a := b + ((a + fn(b,c,d) + X[k] + T[t+1]) <<< s)`, the
rotation as a right rotation by `32 - s`. The additions are in the order of
the specification. -/
def step (t : Nat) : List Instr :=
  let a := var t 0; let b := var t 1; let c := var t 2; let d := var t 3
  fn (t / 16) b c d ++ [
    .alu .add a (.reg T0),
    .alu .add a (.mem (at_ .esi (4 * ks.getD t 0))),
    .alu .add a (.imm (Ts.getD t 0)),
    .shift .ror a (32 - rot t),
    .alu .add a (.reg b)]

/-- Operations `0 … n-1`. -/
def steps : Nat → Prog isa
  | 0 => .block []
  | n + 1 => .seq (steps n) (.block (step n))

/-- The callee-saved registers we use, and where they are saved. -/
def saved : List (Reg × Nat) := [(.ebx, 0), (.esi, 4), (.edi, 8), (.ebp, 12)]

/-- Save the callee-saved registers, load the block pointer and count, and
set ZF if there are no blocks. -/
def prologue : List Instr :=
  [.mov .eax (.mem (at_ .esp 16))] ++
  saved.map (fun (r, d) => .store (at_ .eax d) r) ++
  [.mov .esi (.mem (at_ .esp 8)), .mov .ebp (.mem (at_ .esp 12)), .alu .test .ebp (.reg .ebp)]

/-- Restore the callee-saved registers. -/
def epilogue : List Instr :=
  .mov .eax (.mem (at_ .esp 16)) :: saved.map (fun (r, d) => .mov r (.mem (at_ .eax d)))

/-- Load the MD buffer (`64 % 4 = 0`, so the words are in the same registers
after the 64 operations). -/
def load : List Instr :=
  .mov .edi (.mem (at_ .esp 4)) :: (List.range 4).map fun k => .mov (var 0 k) (.mem (at_ .edi (4 * k)))

/-- Add the words into the MD buffer. -/
def update : List Instr :=
  .mov .edi (.mem (at_ .esp 4)) ::
  ((List.range 4).map (fun k => .alu .add (var 0 k) (.mem (at_ .edi (4 * k)))) ++
    (List.range 4).map (fun k => .store (at_ .edi (4 * k)) (var 0 k)))

/-- Advance to the next block and decrement the count (setting ZF when it hits 0). -/
def advance : List Instr := [.alu .add .esi (.imm 64), .alu .sub .ebp (.imm 1)]

/-- One block. -/
def body : Prog isa := .seq (.block load) (.seq (steps 64) (.block (update ++ advance)))

def compress : Prog isa :=
  .seq (.block prologue) (.seq (.ite .e (.block []) (.loop body .ne)) (.block epilogue))

end VG.Impl.Md5.X86
