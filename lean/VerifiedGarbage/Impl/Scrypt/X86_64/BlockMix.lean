import VerifiedGarbage.Impl.Scrypt.X86_64.Salsa

/-!
# scryptBlockMix: x86-64 implementation

`blockmix(b = rdi, r = rsi, y = rdx, ry = rcx, scratch = r8)` writes
scryptBlockMix (RFC 7914 §4) of the `128 * r` bytes at `b` to the `128 * r`
bytes at `y`.

Step 2's `Y[i]` go straight to their places in step 3's output: `Y[2k]` to
`y + 64k` and `Y[2k + 1]` to `y + 64 (r + k)`. Each is computed in place:
`T = X xor B[i]` is written there, and `vg_salsa20_8` replaces it by
`Salsa (T)`. `X` is then the block just written (initially `B[2r - 1]`).
The loop runs once for each pair `(2k, 2k + 1)`.

`scratch` (128 bytes) holds Salsa20/8's working space (`[0, 64)`) and our
caller's `rbx, rbp, r12–r15` (`[64, 112)`). Across the calls, which
preserve them, `rbx` is `B[2k]`, `rbp` is `y + 64k`, `r12` is
`y + 64 (r + k)`, `r13` is `scratch`, `r14` counts the pairs left and `r15`
is `X`. Every address is one of these plus a constant, and the only branch
is on the count, so only the pointers and `r` affect timing.
-/

namespace VG.Impl.Scrypt.X86_64

open VG.X86_64

/-- The callee-saved registers we use, and where they are saved in `scratch`.
`r13` is last: the epilogue reads the others through it. -/
def bmSaved : List (Reg × Nat) :=
  [(.rbx, 64), (.rbp, 72), (.r12, 80), (.r14, 88), (.r15, 96), (.r13, 104)]

/-- Word `k` (of 8 bytes) of `[dst] ← [x] xor [src]`. -/
def xorW (dst x src : Reg) (k : Nat) : List Instr :=
  [.mov .rax (.mem (at_ x (8 * k))), .alu .xor .rax (.mem (at_ src (8 * k))),
    .store (at_ dst (8 * k)) .rax]

/-- The 64 bytes `[dst] ← [x] xor [src]`. -/
def xor64 (dst x src : Reg) : List Instr := (List.range 8).flatMap (xorW dst x src)

/-- `vg_salsa20_8(dst, scratch)`. -/
def salsaAt (salsa : Prog isa) (dst : Reg) : Prog isa :=
  .seq (.block [.mov .rdi (.reg dst), .mov .rsi (.reg .r13)]) (.call "vg_salsa20_8" salsa)

/-- `rsi ← 64 * rsi`, by doubling. -/
def times64 : List Instr := (List.range 6).map fun _ => .alu .add .rsi (.reg .rsi)

/-- Saving our caller's registers and setting up ours: `rsi = 64 r`,
`r12 = y + 64 r`, `r15 = b + 128 r - 64` (`B[2r - 1]`). -/
def bmPrologue : List Instr :=
  bmSaved.map (fun (r, d) => .store (at_ .r8 d) r) ++
    [.mov .r14 (.reg .rsi), .mov .rbx (.reg .rdi), .mov .rbp (.reg .rdx), .mov .r13 (.reg .r8)] ++
    times64 ++
    [.mov .r12 (.reg .rdx), .alu .add .r12 (.reg .rsi),
     .mov .r15 (.reg .rdi), .alu .add .r15 (.reg .rsi), .alu .add .r15 (.reg .rsi),
     .alu .sub .r15 (.imm 64)]

/-- One pair: `Y[2k]` from `X` and `B[2k]`, then `Y[2k + 1]` from it and
`B[2k + 1]`; then the pointers move on and the count goes down. -/
def bmBody (salsa : Prog isa) : Prog isa :=
  .seq (.block (xor64 .rbp .r15 .rbx)) <|
  .seq (salsaAt salsa .rbp) <|
  .seq (.block (.alu .add .rbx (.imm 64) :: xor64 .r12 .rbp .rbx)) <|
  .seq (salsaAt salsa .r12)
    (.block [.mov .r15 (.reg .r12), .alu .add .rbx (.imm 64), .alu .add .rbp (.imm 64),
      .alu .add .r12 (.imm 64), .alu .sub .r14 (.imm 1)])

/-- Restoring our caller's registers. -/
def bmEpilogue : List Instr := bmSaved.map fun (r, d) => .mov r (.mem (at_ .r13 d))

def blockMixWith (salsa : Prog isa) : Prog isa :=
  .seq (.block bmPrologue) (.seq (.loop (bmBody salsa) .ne) (.block bmEpilogue))

def blockMix : Prog isa := blockMixWith salsa

end VG.Impl.Scrypt.X86_64
