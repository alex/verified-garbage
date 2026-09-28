import VerifiedGarbage.Impl.Scrypt.Arm.Salsa

/-!
# scryptBlockMix: 32-bit ARM implementation

`blockmix(b = r0, r = r1, y = r2, ry = r3, scratch = [sp])` writes
scryptBlockMix (RFC 7914 §4) of the `128 * r` bytes at `b` to the `128 * r`
bytes at `y`.

As on AArch64 (`Impl/Scrypt/AArch64/BlockMix.lean`), step 2's `Y[i]` go
straight to their places in step 3's output: `Y[2k]` to `y + 64k` and
`Y[2k + 1]` to `y + 64 (r + k)`. Each is computed in place: `T = X xor B[i]`
is written there, and `vg_salsa20_8` replaces it by `Salsa (T)`. `X` is then
the block just written (initially `B[2r - 1]`). The loop runs once for each
pair `(2k, 2k + 1)`.

`scratch` (128 bytes) holds Salsa20/8's working space (`[0, 64)`) and our
caller's `r4`–`r9` and our return address (`[64, 92)`), which each call
replaces: there is no stack frame. Across the calls, which preserve them,
`r4` is `B[2k]`, `r5` is `y + 64k`, `r6` is `y + 64 (r + k)`, `r7` is
`scratch`, `r8` counts the pairs left and `r9` is `X`; `r2` and `r3` are
temporaries. Every address is one of these plus a constant, and the only
branch is on the count, so only the pointers and `r` affect timing.
-/

namespace VG.Impl.Scrypt.Arm

open VG.Arm

/-- The registers we save, and where they are saved in `scratch`. `r7` is
last: the epilogue reads the others through it. -/
def bmSaved : List (Reg × Nat) :=
  [(.r4, 64), (.r5, 68), (.r6, 72), (.r8, 76), (.r9, 80), (.lr, 84), (.r7, 88)]

/-- Word `k` of `[dst] ← [x] xor [src]`. -/
def xorW (dst x src : Reg) (k : Nat) : List Instr :=
  [.ldr .r2 x (4 * k), .ldr .r3 src (4 * k), .dp .eor .r2 .r2 (.reg .r3), .str .r2 dst (4 * k)]

/-- The 64 bytes `[dst] ← [x] xor [src]`. -/
def xor64 (dst x src : Reg) : List Instr := (List.range 16).flatMap (xorW dst x src)

/-- `vg_salsa20_8(dst, scratch)`. -/
def salsaAt (salsa : Prog isa) (dst : Reg) : Prog isa :=
  .seq (.block [.mov .r0 (.reg dst), .mov .r1 (.reg .r7)]) (.call "vg_salsa20_8" salsa)

/-- Saving our caller's registers and our return address, and setting up
ours: `r6 = y + 64 r`, `r9 = b + 128 r - 64` (`B[2r - 1]`). -/
def bmPrologue : List Instr :=
  .ldrSp .r12 0 :: bmSaved.map (fun (r, d) => .str r .r12 d) ++
    [.mov .r8 (.reg .r1), .mov .r4 (.reg .r0), .mov .r5 (.reg .r2), .mov .r7 (.reg .r12),
     .dp .add .r6 .r2 (.shifted .r1 .lsl 6), .dp .add .r9 .r0 (.shifted .r1 .lsl 7),
     .dp .sub .r9 .r9 (.imm 64)]

/-- One pair: `Y[2k]` from `X` and `B[2k]`, then `Y[2k + 1]` from it and
`B[2k + 1]`; then the pointers move on and the count goes down. -/
def bmBody (salsa : Prog isa) : Prog isa :=
  .seq (.block (xor64 .r5 .r9 .r4)) <|
  .seq (salsaAt salsa .r5) <|
  .seq (.block (.dp .add .r4 .r4 (.imm 64) :: xor64 .r6 .r5 .r4)) <|
  .seq (salsaAt salsa .r6)
    (.block [.mov .r9 (.reg .r6), .dp .add .r4 .r4 (.imm 64), .dp .add .r5 .r5 (.imm 64),
      .dp .add .r6 .r6 (.imm 64), .subs .r8 .r8 (.imm 1)])

/-- Restoring our caller's registers and our return address. -/
def bmEpilogue : List Instr := bmSaved.map fun (r, d) => .ldr r .r7 d

def blockMixWith (salsa : Prog isa) : Prog isa :=
  .seq (.block bmPrologue) (.seq (.loop (bmBody salsa) .ne) (.block bmEpilogue))

def blockMix : Prog isa := blockMixWith salsa

end VG.Impl.Scrypt.Arm
