import VerifiedGarbage.Spec.Sha3
import VerifiedGarbage.Impl.Sha3.Tables
import VerifiedGarbage.TCB.X86_64.Isa

/-!
# Keccak-f[1600]: x86-64 implementation

`vg_keccak_f1600(state = rdi, scratch = rsi)`.

`scratch` (512 bytes) is laid out as:

* `[0, 200)`: a second state, which the rounds alternate with `state`: each
  round reads one (`src`) and writes the other (`dst`), so after the 24
  rounds the result is back in `state`;
* `[200, 392)`: the 24 round constants, stored by the prologue;
* `[392, 440)`: the saved `rbx, rbp, r12–r15`.

A round keeps `src` in `rdi`, `dst` in `rsi`, a pointer to its round
constant in `rdx` and the end of the round constants in `rcx`, and swaps
`rdi` and `rsi` at its end. It computes the five column parities `C[x]`
(θ) into `rax, rbx, rbp, r8, r9`, then `D[x]` into `r10–r14`; then, for
each plane `y` of the output, the five lanes `B[x]` of `π(ρ(θ(A)))` in that
plane into `rax, rbx, rbp, r8, r9`, and stores `B[x] ⊕ (¬B[x+1] ∧ B[x+2])`
(χ, and ι for lane 0), computed in `r15`, to `dst`.

The loop runs two rounds per iteration, so that `rdi` and `rsi` hold the
same pointers at the start of every iteration: this lets the constant-time
analysis see that the saved registers are not overwritten, so that a caller
gets its own public values back in them.

Every address is a pointer plus a constant, and the only branch is the
round loop's, so only the pointers can affect timing.
-/

namespace VG.Impl.Sha3.X86_64

open VG.X86_64
open VG.Impl.Sha3 (rhoOff piSrc)

def at_ (b : Reg) (d : Nat) : MemOp := { base := b, disp := d }

/-- The register of `C[x]`, and then of `B[x]`. -/
def creg (x : Nat) : Reg := [Reg.rax, .rbx, .rbp, .r8, .r9].getD x .rax

/-- The register of `D[x]`. -/
def dreg (x : Nat) : Reg := [Reg.r10, .r11, .r12, .r13, .r14].getD x .r10

/-- The temporary of χ. -/
def T : Reg := .r15

/-- Lane `i` of the state at `b`. -/
def lane (b : Reg) (i : Nat) : MemOp := at_ b (8 * i)

/-- `C[x] = A[x, 0] ⊕ … ⊕ A[x, 4]`. -/
def column (x : Nat) : List Instr :=
  [.mov (creg x) (.mem (lane .rdi x)), .alu .xor (creg x) (.mem (lane .rdi (x + 5))),
    .alu .xor (creg x) (.mem (lane .rdi (x + 10))), .alu .xor (creg x) (.mem (lane .rdi (x + 15))),
    .alu .xor (creg x) (.mem (lane .rdi (x + 20)))]

/-- `D[x] = ROTL¹(C[x + 1]) ⊕ C[x - 1]` (a rotation left by 1 is one right by 63). -/
def dcol (x : Nat) : List Instr :=
  [.mov (dreg x) (.reg (creg ((x + 1) % 5))), .shift .ror (dreg x) 63,
    .alu .xor (dreg x) (.reg (creg ((x + 4) % 5)))]

/-- `B[x] = ROTL^ρ(A[piSrc x y] ⊕ D[(x + 3y) mod 5])` for plane `y`. -/
def laneB (x y : Nat) : List Instr :=
  [.mov (creg x) (.mem (lane .rdi (piSrc x y))), .alu .xor (creg x) (.reg (dreg ((x + 3 * y) % 5)))] ++
    if rhoOff (piSrc x y) = 0 then [] else [.shift .ror (creg x) (64 - rhoOff (piSrc x y))]

/-- Lane `(x, y)` of the output: `B[x] ⊕ (¬B[x+1] ∧ B[x+2])`, and for lane 0
the round constant at `rdx`. (`¬` is an XOR with all ones, the sign-extended
immediate `-1`.) -/
def chi (x y : Nat) : List Instr :=
  [.mov T (.reg (creg ((x + 1) % 5))), .alu .xor T (.imm 0xffffffff),
    .alu .and T (.reg (creg ((x + 2) % 5))), .alu .xor T (.reg (creg x))] ++
    (if x = 0 ∧ y = 0 then [.alu .xor T (.mem (at_ .rdx 0))] else []) ++
    [.store (lane .rsi (x + 5 * y)) T]

/-- Plane `y` of the output. -/
def plane (y : Nat) : List Instr :=
  (List.range 5).flatMap (fun x => laneB x y) ++ (List.range 5).flatMap (fun x => chi x y)

/-- One round from `rdi` to `rsi`; then swap them, and advance to the next
round constant (setting ZF after the last). -/
def round : List Instr :=
  (List.range 5).flatMap column ++ (List.range 5).flatMap dcol ++ (List.range 5).flatMap plane ++
    [.mov .rax (.reg .rdi), .mov .rdi (.reg .rsi), .mov .rsi (.reg .rax),
      .alu .add .rdx (.imm 8), .alu .cmp .rdx (.reg .rcx)]

/-- The callee-saved registers we use, and where they are saved. -/
def saved : List (Reg × Nat) :=
  [(.rbx, 392), (.rbp, 400), (.r12, 408), (.r13, 416), (.r14, 424), (.r15, 432)]

/-- Save them, store the round constants, and point `rdi` at `state`,
`rsi` at the second state, `rdx` at the first round constant and `rcx` past
the last. -/
def prologue : List Instr :=
  saved.map (fun (r, d) => .store (at_ .rsi d) r) ++
  (List.range 24).flatMap (fun k => [.movImm64 .rax (Spec.Sha3.RC k), .store (at_ .rsi (200 + 8 * k)) .rax]) ++
  [.mov .rdx (.reg .rsi), .alu .add .rdx (.imm 200), .mov .rcx (.reg .rsi), .alu .add .rcx (.imm 392)]

def restore : List Instr := saved.map fun (r, d) => .mov r (.mem (at_ .rsi d))

def permute : Prog isa :=
  .seq (.block prologue) (.seq (.loop (.block (round ++ round)) .ne) (.block restore))

end VG.Impl.Sha3.X86_64
