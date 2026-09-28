import VerifiedGarbage.Impl.Scrypt.AArch64.Salsa

/-!
# scryptBlockMix: AArch64 implementation

`blockmix(b = x0, r = x1, y = x2, ry = x3, scratch = x4)` writes
scryptBlockMix (RFC 7914 §4) of the `128 * r` bytes at `b` to the `128 * r`
bytes at `y`.

As on x86-64 (`Impl/Scrypt/X86_64/BlockMix.lean`), step 2's `Y[i]` go straight
to their places in step 3's output: `Y[2k]` to `y + 64k` and `Y[2k + 1]` to
`y + 64 (r + k)`. Each is computed in place: `T = X xor B[i]` is written there,
and `vg_salsa20_8` replaces it by `Salsa (T)`. `X` is then the block just
written (initially `B[2r - 1]`). The loop runs once for each pair
`(2k, 2k + 1)`.

`scratch` (128 bytes) holds Salsa20/8's working space (`[0, 64)`) and our
caller's `x19`–`x24` (`[64, 112)`); our return address (`x30`), which each
call replaces, is saved in a stack frame around the whole function. Across
the calls, which preserve them, `x19` is `B[2k]`, `x20` is `y + 64k`, `x21`
is `y + 64 (r + k)`, `x22` is `scratch`, `x23` counts the pairs left and
`x24` is `X`. Every address is one of these plus a constant, and the only
branch is on the count, so only the pointers and `r` affect timing.
-/

namespace VG.Impl.Scrypt.AArch64

open VG.AArch64

/-- `mov d, n` (as `add d, n, #0`). -/
def mov (d n : Reg) : Instr := .addImm .x d n 0

/-- The callee-saved registers we use, and where they are saved in `scratch`.
`x22` is last: the epilogue reads the others through it. -/
def bmSaved : List (Reg × Nat) :=
  [(.x19, 64), (.x20, 72), (.x21, 80), (.x23, 88), (.x24, 96), (.x22, 104)]

/-- Word `k` (of 8 bytes) of `[dst] ← [x] xor [src]`. -/
def xorW (dst x src : Reg) (k : Nat) : List Instr :=
  [.ldr .x .x9 x (8 * k), .ldr .x .x10 src (8 * k), .logic .eor .x .x9 .x9 .x10,
    .str .x .x9 dst (8 * k)]

/-- The 64 bytes `[dst] ← [x] xor [src]`. -/
def xor64 (dst x src : Reg) : List Instr := (List.range 8).flatMap (xorW dst x src)

/-- `vg_salsa20_8(dst, scratch)`. -/
def salsaAt (salsa : Prog isa) (dst : Reg) : Prog isa :=
  .seq (.block [mov .x0 dst, mov .x1 .x22]) (.call "vg_salsa20_8" salsa)

/-- Saving our caller's registers and setting up ours: `x21 = y + 64 r`,
`x24 = b + 128 r - 64` (`B[2r - 1]`). -/
def bmPrologue : List Instr :=
  bmSaved.map (fun (r, d) => .str .x r .x4 d) ++
    [mov .x23 .x1, mov .x19 .x0, mov .x20 .x2, mov .x22 .x4,
     .lsl .x .x9 .x1 6, .add .x .x21 .x2 .x9,
     .lsl .x .x9 .x1 7, .add .x .x24 .x0 .x9, .subImm .x .x24 .x24 64]

/-- One pair: `Y[2k]` from `X` and `B[2k]`, then `Y[2k + 1]` from it and
`B[2k + 1]`; then the pointers move on and the count goes down. -/
def bmBody (salsa : Prog isa) : Prog isa :=
  .seq (.block (xor64 .x20 .x24 .x19)) <|
  .seq (salsaAt salsa .x20) <|
  .seq (.block (.addImm .x .x19 .x19 64 :: xor64 .x21 .x20 .x19)) <|
  .seq (salsaAt salsa .x21)
    (.block [mov .x24 .x21, .addImm .x .x19 .x19 64, .addImm .x .x20 .x20 64,
      .addImm .x .x21 .x21 64, .subImm .x .x23 .x23 1])

/-- Restoring our caller's registers. -/
def bmEpilogue : List Instr := bmSaved.map fun (r, d) => .ldr .x r .x22 d

def blockMixMain (salsa : Prog isa) : Prog isa :=
  .seq (.block bmPrologue) (.seq (.loop (bmBody salsa) (.nonzero .x .x23)) (.block bmEpilogue))

def blockMixWith (salsa : Prog isa) : Prog isa :=
  .frame (.push .x30) (blockMixMain salsa) (.pop .x30)

def blockMix : Prog isa := blockMixWith salsa

end VG.Impl.Scrypt.AArch64
