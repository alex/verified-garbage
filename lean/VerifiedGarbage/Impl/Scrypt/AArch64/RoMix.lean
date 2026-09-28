import VerifiedGarbage.Impl.Scrypt.AArch64.BlockMix

/-!
# scryptROMix: AArch64 implementation

`romix(b = x0, r = x1, v = x2, vlen = x3, scratch = x4, slen = x5)`
replaces the `128 * r` bytes at `b` by scryptROMix (RFC 7914 §5) of them,
with `N = vlen / r`, a power of two. `X` stays in `b`.

As on x86-64 (`Impl/Scrypt/X86_64/RoMix.lean`), step 2 runs `N` times:
`V[i] = X` (a copy), then `X = scryptBlockMix (V[i])`. Step 3 runs `N`
times: `j = Integerify (X) mod N` (the low 8 bytes of `X`'s last 64-byte
block, masked with `N - 1`), then `T = X xor V[j]`, then
`X = scryptBlockMix (T)`. The address of `V[j]` is `v + j * 128 r` (`madd`).

`scratch` (`128 (r + 2)` bytes) holds scryptBlockMix's working space
(`[0, 128)`), our caller's `x19`–`x24` and our return address `x30`
(`[128, 184)`: there is no stack frame), `N` (`[184, 192)`) and `T`
(`[192, 192 + 128 r)`). Across the calls, which preserve them, `x19` is
`b`, `x20` is `v`, `x21` is `scratch`, `x22` is `128 r` and `x23` counts the
iterations left; `x24` is `V[i]` in step 2 and `N - 1` in step 3.

Every branch and address depends only on the pointers, `r`, `N` and the
indices `j`: the contract declares that the function leaks the `j`.
-/

namespace VG.Impl.Scrypt.AArch64

open VG.AArch64

/-- The registers we save, and where they are saved in `scratch`. `x21` is
last: the epilogue reads the others through it. -/
def rmSaved : List (Reg × Nat) :=
  [(.x19, 128), (.x20, 136), (.x22, 144), (.x23, 152), (.x24, 160), (.x30, 168), (.x21, 176)]

/-- The 8-byte words `[x10] ← [x9]`, `x11` of them. -/
def copyLoop : Prog isa :=
  .loop (.block [.ldr .x .x12 .x9 0, .str .x .x12 .x10 0, .addImm .x .x9 .x9 8,
    .addImm .x .x10 .x10 8, .subImm .x .x11 .x11 1]) (.nonzero .x .x11)

/-- The 8-byte words `[x11] ← [x9] xor [x10]`, `x12` of them. -/
def xorLoop : Prog isa :=
  .loop (.block [.ldr .x .x13 .x9 0, .ldr .x .x14 .x10 0, .logic .eor .x .x13 .x13 .x14,
    .str .x .x13 .x11 0, .addImm .x .x9 .x9 8, .addImm .x .x10 .x10 8, .addImm .x .x11 .x11 8,
    .subImm .x .x12 .x12 1]) (.nonzero .x .x12)

/-- Saving our caller's registers; `x19 = b`, `x20 = v`, `x21 = scratch`,
`x22 = 128 r`; `x9 = r`, `x10 = 1`, `x11 = 2 vlen` for `nLoop`. -/
def rmPrologue : List Instr :=
  rmSaved.map (fun (r, d) => .str .x r .x4 d) ++
    [mov .x19 .x0, mov .x20 .x2, mov .x21 .x4, .lsl .x .x22 .x1 7,
     mov .x9 .x1, .movz .x .x10 1 0, .add .x .x11 .x3 .x3]

/-- `x10 ← 2 N`: doubling `x9` (from `r`) and `x10` (from 1) until `x9 = 2 vlen`. -/
def nLoop : Prog isa :=
  .loop (.block [.add .x .x9 .x9 .x9, .add .x .x10 .x10 .x10, .sub .x .x12 .x9 .x11])
    (.nonzero .x .x12)

/-- `N` to `scratch` and the count; `x24 = v`. -/
def rmSetup : List Instr :=
  [.lsr .x .x10 .x10 1, .str .x .x10 .x21 184, mov .x23 .x10, mov .x24 .x20]

/-- `vg_scrypt_blockmix(src, r, dst = b, r, scratch)`. -/
def blockMixTo (blockMix : Prog isa) (src : List Instr) : Prog isa :=
  .seq (.block (src ++ [.lsr .x .x1 .x22 7, mov .x2 .x19, mov .x3 .x1, mov .x4 .x21]))
    (.call "vg_scrypt_blockmix" blockMix)

/-- Step 2, once: `V[i] = X`, `X = scryptBlockMix (V[i])`. -/
def step2 (blockMix : Prog isa) : Prog isa :=
  .seq (.block [mov .x9 .x19, mov .x10 .x24, .lsr .x .x11 .x22 3]) <|
  .seq copyLoop <|
  .seq (blockMixTo blockMix [mov .x0 .x24])
    (.block [.add .x .x24 .x24 .x22, .subImm .x .x23 .x23 1])

/-- Between the steps: the count is `N` again, and `x24 = N - 1`. -/
def rmMid : List Instr :=
  [.ldr .x .x23 .x21 184, .subImm .x .x24 .x23 1]

/-- `x9 ← j`: the low 8 bytes of `X`'s last 64-byte block, masked with `N - 1`. -/
def jBlock : List Instr :=
  [.add .x .x9 .x19 .x22, .subImm .x .x9 .x9 64, .ldr .x .x9 .x9 0, .logic .and .x .x9 .x9 .x24]

/-- Step 3, once: `j`; `x10 = V[j]`; `T = X xor V[j]`; `X = scryptBlockMix (T)`. -/
def step3 (blockMix : Prog isa) : Prog isa :=
  .seq (.block jBlock) <|
  .seq (.block [.madd .x .x10 .x9 .x22 .x20, mov .x9 .x19, .addImm .x .x11 .x21 192,
    .lsr .x .x12 .x22 3]) <|
  .seq xorLoop <|
  .seq (blockMixTo blockMix [.addImm .x .x0 .x21 192])
    (.block [.subImm .x .x23 .x23 1])

/-- Restoring our caller's registers and our return address. -/
def rmEpilogue : List Instr := rmSaved.map fun (r, d) => .ldr .x r .x21 d

def roMixWith (blockMix : Prog isa) : Prog isa :=
  .seq (.block rmPrologue) <|
  .seq nLoop <|
  .seq (.block rmSetup) <|
  .seq (.loop (step2 blockMix) (.nonzero .x .x23)) <|
  .seq (.block rmMid) <|
  .seq (.loop (step3 blockMix) (.nonzero .x .x23))
    (.block rmEpilogue)

def roMix : Prog isa := roMixWith blockMix

end VG.Impl.Scrypt.AArch64
