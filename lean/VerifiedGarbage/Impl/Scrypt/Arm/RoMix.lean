import VerifiedGarbage.Impl.Scrypt.Arm.BlockMix

/-!
# scryptROMix: 32-bit ARM implementation

`romix(b = r0, r = r1, v = r2, vlen = r3, scratch = [sp], slen = [sp + 4])`
replaces the `128 * r` bytes at `b` by scryptROMix (RFC 7914 §5) of them,
with `N = vlen / r`, a power of two. `X` stays in `b`.

As on x86-64 and AArch64 (`Impl/Scrypt/X86_64/RoMix.lean`,
`Impl/Scrypt/AArch64/RoMix.lean`), step 2 runs `N` times: `V[i] = X` (a
copy), then `X = scryptBlockMix (V[i])`. Step 3 runs `N` times:
`j = Integerify (X) mod N` (the low 4 bytes of `X`'s last 64-byte block,
masked with `N - 1`: `N` is below `2^32`), then `T = X xor V[j]`, then
`X = scryptBlockMix (T)`. The model has no multiplication, so, as on
x86-64, the address of `V[j]`, `v + j * 128 r`, is computed by shifting and
adding over the bits of `j`.

`vg_scrypt_blockmix`'s stack argument, its scratch space, is ours: we make
the calls with the stack pointer we were entered with. `scratch`
(`128 (r + 2)` bytes) holds scryptBlockMix's working space (`[0, 128)`),
our caller's `r4`–`r9` and our return address (`[128, 156)`: there is no
stack frame), `N` (`[156, 160)`) and `T` (`[192, 192 + 128 r)`). Across the
calls, which preserve them, `r4` is `b`, `r5` is `v`, `r6` is `scratch`,
`r7` is `128 r` and `r8` counts the iterations left; `r9` is `V[i]` in step
2 and `N - 1` in step 3.

Every branch and address depends only on the pointers, `r`, `N` and the
indices `j`: the contract declares that the function leaks the `j`.
-/

namespace VG.Impl.Scrypt.Arm

open VG.Arm

/-- The registers we save, and where they are saved in `scratch`. `r6` is
last: the epilogue reads the others through it. -/
def rmSaved : List (Reg × Nat) :=
  [(.r4, 128), (.r5, 132), (.r7, 136), (.r8, 140), (.r9, 144), (.lr, 148), (.r6, 152)]

/-- The words `[r1] ← [r0]`, `r2` of them. -/
def copyLoop : Prog isa :=
  .loop (.block [.ldr .r3 .r0 0, .str .r3 .r1 0, .dp .add .r0 .r0 (.imm 4),
    .dp .add .r1 .r1 (.imm 4), .subs .r2 .r2 (.imm 1)]) .ne

/-- The words `[r2] ← [r0] xor [r1]`, `r3` of them. -/
def xorLoop : Prog isa :=
  .loop (.block [.ldr .r12 .r0 0, .ldr .lr .r1 0, .dp .eor .r12 .r12 (.reg .lr), .str .r12 .r2 0,
    .dp .add .r0 .r0 (.imm 4), .dp .add .r1 .r1 (.imm 4), .dp .add .r2 .r2 (.imm 4),
    .subs .r3 .r3 (.imm 1)]) .ne

/-- `r1 ← r1 + r0 * r2`, over the bits of `r0`. -/
def mulLoop : Prog isa :=
  .loop (.seq (.block [.dp .and .r3 .r0 (.imm 1), .cmp .r3 (.imm 0)]) <|
    .seq (.ite .ne (.block [.dp .add .r1 .r1 (.reg .r2)]) (.block []))
      (.block [.dp .add .r2 .r2 (.reg .r2), .mov .r0 (.shifted .r0 .lsr 1), .cmp .r0 (.imm 0)])) .ne

/-- Saving our caller's registers and our return address; `r4 = b`,
`r5 = v`, `r6 = scratch`, `r7 = 128 r`; `r0 = r`, `r1 = 1`, `r2 = 2 vlen`
for `nLoop`. -/
def rmPrologue : List Instr :=
  .ldrSp .r12 0 :: rmSaved.map (fun (r, d) => .str r .r12 d) ++
    [.mov .r4 (.reg .r0), .mov .r5 (.reg .r2), .mov .r6 (.reg .r12), .mov .r7 (.shifted .r1 .lsl 7),
     .mov .r0 (.reg .r1), .mov .r1 (.imm 1), .dp .add .r2 .r3 (.reg .r3)]

/-- `r1 ← 2 N`: doubling `r0` (from `r`) and `r1` (from 1) until `r0 = 2 vlen`. -/
def nLoop : Prog isa :=
  .loop (.block [.dp .add .r0 .r0 (.reg .r0), .dp .add .r1 .r1 (.reg .r1), .cmp .r0 (.reg .r2)]) .ne

/-- `N` to `scratch` and the count; `r9 = v`. -/
def rmSetup : List Instr :=
  [.mov .r1 (.shifted .r1 .lsr 1), .str .r1 .r6 156, .mov .r8 (.reg .r1), .mov .r9 (.reg .r5)]

/-- `vg_scrypt_blockmix(src, r, dst = b, r, scratch)`, `scratch` being our
own stack argument. -/
def blockMixTo (blockMix : Prog isa) (src : List Instr) : Prog isa :=
  .seq (.block (src ++ [.mov .r1 (.shifted .r7 .lsr 7), .mov .r2 (.reg .r4), .mov .r3 (.reg .r1)]))
    (.call "vg_scrypt_blockmix" blockMix)

/-- Step 2, once: `V[i] = X`, `X = scryptBlockMix (V[i])`. -/
def step2 (blockMix : Prog isa) : Prog isa :=
  .seq (.block [.mov .r0 (.reg .r4), .mov .r1 (.reg .r9), .mov .r2 (.shifted .r7 .lsr 2)]) <|
  .seq copyLoop <|
  .seq (blockMixTo blockMix [.mov .r0 (.reg .r9)])
    (.block [.dp .add .r9 .r9 (.reg .r7), .subs .r8 .r8 (.imm 1)])

/-- Between the steps: the count is `N` again, and `r9 = N - 1`. -/
def rmMid : List Instr := [.ldr .r8 .r6 156, .dp .sub .r9 .r8 (.imm 1)]

/-- `r0 ← j`: the low 4 bytes of `X`'s last 64-byte block, masked with `N - 1`. -/
def jBlock : List Instr :=
  [.dp .add .r0 .r4 (.reg .r7), .dp .sub .r0 .r0 (.imm 64), .ldr .r0 .r0 0,
    .dp .and .r0 .r0 (.reg .r9)]

/-- Step 3, once: `j`; `r1 = V[j]`; `T = X xor V[j]`; `X = scryptBlockMix (T)`. -/
def step3 (blockMix : Prog isa) : Prog isa :=
  .seq (.block jBlock) <|
  .seq (.block [.mov .r1 (.reg .r5), .mov .r2 (.reg .r7)]) <|
  .seq mulLoop <|
  .seq (.block [.mov .r0 (.reg .r4), .dp .add .r2 .r6 (.imm 192), .mov .r3 (.shifted .r7 .lsr 2)]) <|
  .seq xorLoop <|
  .seq (blockMixTo blockMix [.dp .add .r0 .r6 (.imm 192)])
    (.block [.subs .r8 .r8 (.imm 1)])

/-- Restoring our caller's registers and our return address. -/
def rmEpilogue : List Instr := rmSaved.map fun (r, d) => .ldr r .r6 d

def roMixWith (blockMix : Prog isa) : Prog isa :=
  .seq (.block rmPrologue) <|
  .seq nLoop <|
  .seq (.block rmSetup) <|
  .seq (.loop (step2 blockMix) .ne) <|
  .seq (.block rmMid) <|
  .seq (.loop (step3 blockMix) .ne)
    (.block rmEpilogue)

def roMix : Prog isa := roMixWith blockMix

end VG.Impl.Scrypt.Arm
