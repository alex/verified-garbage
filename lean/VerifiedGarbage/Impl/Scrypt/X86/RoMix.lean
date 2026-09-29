import VerifiedGarbage.Impl.Scrypt.X86.BlockMix

/-!
# scryptROMix: x86 (32-bit) implementation

`romix(b = [esp + 4], r = [esp + 8], v = [esp + 12], vlen = [esp + 16],
scratch = [esp + 20], slen = [esp + 24])`, every argument on the stack
(cdecl), replaces the `128 * r` bytes at `b` by scryptROMix (RFC 7914 §5) of
them, with `N = vlen / r`, a power of two. `X` stays in `b`.

As on the other targets (`Impl/Scrypt/Arm/RoMix.lean`), step 2 runs `N`
times: `V[i] = X` (a copy), then `X = scryptBlockMix (V[i])`. Step 3 runs `N`
times: `j = Integerify (X) mod N` (the low 4 bytes of `X`'s last 64-byte
block, masked with `N - 1`: `N` is below `2^32`), then `T = X xor V[j]`, then
`X = scryptBlockMix (T)`. `N` is computed by doubling, and the address of
`V[j]`, `v + j * 128 r`, with `mul`.

`vg_scrypt_blockmix` preserves `ebx`, `esi`, `edi` and `ebp`, so our
variables live there across it: `ebx` counts the iterations left, `ebp` is
`N`, and `esi` is `V[i]` in step 2 and `T` in step 3, the source of the
call; `edi` is a temporary, as are `eax`, `ecx` and `edx`. The pointers and
`r` are read from the arguments when needed. `scratch` (`128 (r + 2)` bytes)
holds scryptBlockMix's working space (`[0, 128)`), our caller's `ebx`,
`esi`, `edi` and `ebp` (`[128, 144)`) and `T` (`[192, 192 + 128 r)`). Each
call of `vg_scrypt_blockmix` pushes its five arguments in a frame of its
own, popped (into `eax`) when it returns: with the return address the call
stores and the stack scryptBlockMix uses, it uses the 36 bytes below `esp`.

Every branch and address depends only on `esp`, the pointers, `r`, `N` and
the indices `j`: the contract declares that the function leaks the `j`.
-/

namespace VG.Impl.Scrypt.X86

open VG.X86

/-- The callee-saved registers, and where they are saved in `scratch`. -/
def rmSaved : List (Reg × Nat) := [(.ebx, 128), (.esi, 132), (.edi, 136), (.ebp, 140)]

/-- The words `[ecx] ← [eax]`, `edx` of them. -/
def copyLoop : Prog isa :=
  .loop (.block [.mov .edi (.mem (at_ .eax 0)), .store (at_ .ecx 0) .edi, .alu .add .eax (.imm 4),
    .alu .add .ecx (.imm 4), .alu .sub .edx (.imm 1)]) .ne

/-- The words `[edx] ← [eax] xor [ecx]`, `edi` of them. -/
def xorLoop : Prog isa :=
  .loop (.block [.mov .esi (.mem (at_ .eax 0)), .alu .xor .esi (.mem (at_ .ecx 0)),
    .store (at_ .edx 0) .esi, .alu .add .eax (.imm 4), .alu .add .ecx (.imm 4), .alu .add .edx (.imm 4),
    .alu .sub .edi (.imm 1)]) .ne

/-- Saving our caller's registers; `eax = r`, `ecx = 1`, `edx = 2 vlen` for
`nLoop`. -/
def rmPrologue : List Instr :=
  .mov .eax (.mem (at_ .esp 20)) :: rmSaved.map (fun (r, d) => .store (at_ .eax d) r) ++
    [.mov .eax (.mem (at_ .esp 8)), .mov .ecx (.imm 1), .mov .edx (.mem (at_ .esp 16)),
     .alu .add .edx (.reg .edx)]

/-- `ecx ← 2 N`: doubling `eax` (from `r`) and `ecx` (from 1) until `eax = 2 vlen`. -/
def nLoop : Prog isa :=
  .loop (.block [.alu .add .eax (.reg .eax), .alu .add .ecx (.reg .ecx), .alu .cmp .eax (.reg .edx)]) .ne

/-- `ebp = N`, the count `ebx = N`, and `esi = v` (`V[0]`). -/
def rmSetup : List Instr :=
  [.shift .shr .ecx 1, .mov .ebp (.reg .ecx), .mov .ebx (.reg .ecx), .mov .esi (.mem (at_ .esp 12))]

/-- The arguments of `vg_scrypt_blockmix(esi, r, b, r, scratch)`. -/
def bmArgs : List Instr :=
  [.mov .eax (.mem (at_ .esp 20)), .mov .ecx (.mem (at_ .esp 8)), .mov .edx (.mem (at_ .esp 4))]

/-- `vg_scrypt_blockmix(esi, r, dst = b, r, scratch)`, its arguments pushed
last to first. -/
def blockMixTo (blockMix : Prog isa) : Prog isa :=
  .seq (.block bmArgs)
    (.frame (.push [.eax, .ecx, .edx, .ecx, .esi]) (.call "vg_scrypt_blockmix" blockMix) (.pop .eax 5))

/-- Step 2, once: `V[i] = X`, `X = scryptBlockMix (V[i])`, `esi = V[i + 1]`. -/
def step2 (blockMix : Prog isa) : Prog isa :=
  .seq (.block (timesR 32 ++ [.mov .edx (.reg .eax), .mov .eax (.mem (at_ .esp 4)), .mov .ecx (.reg .esi)])) <|
  .seq copyLoop <|
  .seq (blockMixTo blockMix)
    (.block (timesR 128 ++ [.alu .add .esi (.reg .eax), .alu .sub .ebx (.imm 1)]))

/-- Between the steps: the count is `N` again. -/
def rmMid : List Instr := [.mov .ebx (.reg .ebp)]

/-- `eax ← j`: the low 4 bytes of `X`'s last 64-byte block, masked with
`N - 1`; `edi = 128 r`. -/
def jBlock : List Instr :=
  timesR 128 ++ [.mov .edi (.reg .eax), .mov .ecx (.mem (at_ .esp 4)), .alu .add .eax (.reg .ecx),
    .alu .sub .eax (.imm 64), .mov .eax (.mem (at_ .eax 0)), .mov .ecx (.reg .ebp), .alu .sub .ecx (.imm 1),
    .alu .and .eax (.reg .ecx)]

/-- `ecx = V[j] = v + j * 128 r`, and the other operands of `xorLoop`:
`eax = X`, `edx = T`, `edi = 32 r` words. -/
def vjBlock : List Instr :=
  [.mul .edi, .mov .ecx (.mem (at_ .esp 12)), .alu .add .ecx (.reg .eax), .mov .eax (.mem (at_ .esp 4)),
    .mov .edx (.mem (at_ .esp 20)), .alu .add .edx (.imm 192), .shift .shr .edi 2]

/-- `esi = T`. -/
def tBlock : List Instr := [.mov .esi (.mem (at_ .esp 20)), .alu .add .esi (.imm 192)]

/-- Step 3, once: `j`; `ecx = V[j]`; `T = X xor V[j]`; `X = scryptBlockMix (T)`. -/
def step3 (blockMix : Prog isa) : Prog isa :=
  .seq (.block jBlock) <|
  .seq (.block vjBlock) <|
  .seq xorLoop <|
  .seq (.block tBlock) <|
  .seq (blockMixTo blockMix)
    (.block [.alu .sub .ebx (.imm 1)])

/-- Restoring our caller's registers. -/
def rmEpilogue : List Instr :=
  .mov .eax (.mem (at_ .esp 20)) :: rmSaved.map fun (r, d) => .mov r (.mem (at_ .eax d))

def roMixWith (blockMix : Prog isa) : Prog isa :=
  .seq (.block rmPrologue) <|
  .seq nLoop <|
  .seq (.block rmSetup) <|
  .seq (.loop (step2 blockMix) .ne) <|
  .seq (.block rmMid) <|
  .seq (.loop (step3 blockMix) .ne)
    (.block rmEpilogue)

def roMix : Prog isa := roMixWith blockMix

end VG.Impl.Scrypt.X86
