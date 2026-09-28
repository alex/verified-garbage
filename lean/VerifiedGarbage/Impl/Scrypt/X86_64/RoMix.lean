import VerifiedGarbage.Impl.Scrypt.X86_64.BlockMix

/-!
# scryptROMix: x86-64 implementation

`romix(b = rdi, r = rsi, v = rdx, vlen = rcx, scratch = r8, slen = r9)`
replaces the `128 * r` bytes at `b` by scryptROMix (RFC 7914 §5) of them,
with `N = vlen / r`, a power of two. `X` stays in `b`.

Step 2 runs `N` times: `V[i] = X` (a copy), then `X = scryptBlockMix (V[i])`.
Step 3 runs `N` times: `j = Integerify (X) mod N` (the low 8 bytes of
`X`'s last 64-byte block, masked with `N - 1`), then `T = X xor V[j]`, then
`X = scryptBlockMix (T)`. The address of `V[j]` is `v + j * 128 r`, computed
by shifting and adding over the bits of `j`.

`scratch` (`128 (r + 2)` bytes) holds scryptBlockMix's working space
(`[0, 128)`), our caller's `rbx, rbp, r12, r14, r15, r13` (`[128, 176)`),
`N` (`[176, 184)`) and `T` (`[192, 192 + 128 r)`). Across the calls, which
preserve them, `rbx` is `b`, `r12` is `v`, `r13` is `scratch`, `r14` is
`128 r` and `r15` counts the iterations left; `rbp` is `V[i]` in step 2 and
`N - 1` in step 3.

Every branch and address depends only on the pointers, `r`, `N` and the
indices `j`: the contract declares that the function leaks the `j`.
-/

namespace VG.Impl.Scrypt.X86_64

open VG.X86_64

/-- The callee-saved registers we use, and where they are saved in `scratch`.
`r13` is last: the epilogue reads the others through it. -/
def rmSaved : List (Reg × Nat) :=
  [(.rbx, 128), (.rbp, 136), (.r12, 144), (.r14, 152), (.r15, 160), (.r13, 168)]

/-- The 8-byte words `[dst] ← [src]`, `rcx` of them. -/
def copyLoop : Prog isa :=
  .loop (.block [.mov .rax (.mem (at_ .rdi 0)), .store (at_ .rsi 0) .rax,
    .alu .add .rdi (.imm 8), .alu .add .rsi (.imm 8), .alu .sub .rcx (.imm 1)]) .ne

/-- The 8-byte words `[r8] ← [rdi] xor [rsi]`, `rcx` of them. -/
def xorLoop : Prog isa :=
  .loop (.block [.mov .rax (.mem (at_ .rdi 0)), .alu .xor .rax (.mem (at_ .rsi 0)),
    .store (at_ .r8 0) .rax, .alu .add .rdi (.imm 8), .alu .add .rsi (.imm 8),
    .alu .add .r8 (.imm 8), .alu .sub .rcx (.imm 1)]) .ne

/-- `rdx ← rdx + rax * rcx`, over the bits of `rax`. -/
def mulLoop : Prog isa :=
  .loop (.seq (.block [.alu .test .rax (.imm 1)]) <|
    .seq (.ite .ne (.block [.alu .add .rdx (.reg .rcx)]) (.block []))
      (.block [.alu .add .rcx (.reg .rcx), .shift .shr .rax 1])) .ne

/-- Saving our caller's registers; `rbx = b`, `r12 = v`, `r13 = scratch`,
`r14 = 128 r`; `rax = 2 r`, `rdx = 2`, `rcx = 2 vlen` for `nLoop`. -/
def rmPrologue : List Instr :=
  rmSaved.map (fun (r, d) => .store (at_ .r8 d) r) ++
    [.mov .rbx (.reg .rdi), .mov .r12 (.reg .rdx), .mov .r13 (.reg .r8), .mov .r14 (.reg .rsi)] ++
    (List.range 7).map (fun _ => .alu .add .r14 (.reg .r14)) ++
    [.mov .rax (.reg .rsi), .mov32 .rdx (.imm 1), .alu .add .rcx (.reg .rcx)]

/-- `rdx ← 2 N`: doubling `rax` (from `r`) and `rdx` (from 1) until `rax = 2 vlen`. -/
def nLoop : Prog isa :=
  .loop (.block [.alu .add .rax (.reg .rax), .alu .add .rdx (.reg .rdx),
    .alu .cmp .rax (.reg .rcx)]) .ne

/-- `N` to `scratch` and the count; `rbp = v`. -/
def rmSetup : List Instr :=
  [.shift .shr .rdx 1, .store (at_ .r13 176) .rdx, .mov .r15 (.reg .rdx), .mov .rbp (.reg .r12)]

/-- `vg_scrypt_blockmix(src, r, dst = b, r, scratch)`. -/
def blockMixTo (blockMix : Prog isa) (src : List Instr) : Prog isa :=
  .seq (.block (src ++ [.mov .rsi (.reg .r14), .shift .shr .rsi 7, .mov .rcx (.reg .rsi),
    .mov .rdx (.reg .rbx), .mov .r8 (.reg .r13)])) (.call "vg_scrypt_blockmix" blockMix)

/-- Step 2, once: `V[i] = X`, `X = scryptBlockMix (V[i])`. -/
def step2 (blockMix : Prog isa) : Prog isa :=
  .seq (.block [.mov .rdi (.reg .rbx), .mov .rsi (.reg .rbp), .mov .rcx (.reg .r14),
    .shift .shr .rcx 3]) <|
  .seq copyLoop <|
  .seq (blockMixTo blockMix [.mov .rdi (.reg .rbp)])
    (.block [.alu .add .rbp (.reg .r14), .alu .sub .r15 (.imm 1)])

/-- Between the steps: the count is `N` again, and `rbp = N - 1`. -/
def rmMid : List Instr :=
  [.mov .r15 (.mem (at_ .r13 176)), .mov .rbp (.reg .r15), .alu .sub .rbp (.imm 1)]

/-- `rax ← j`: the low 8 bytes of `X`'s last 64-byte block, masked with `N - 1`. -/
def jBlock : List Instr :=
  [.mov .rax (.mem { base := .rbx, index := some .r14, disp := -64 }), .alu .and .rax (.reg .rbp)]

/-- Step 3, once: `j`; `rdx = V[j]`; `T = X xor V[j]`; `X = scryptBlockMix (T)`. -/
def step3 (blockMix : Prog isa) : Prog isa :=
  .seq (.block jBlock) <|
  .seq (.block [.mov .rdx (.reg .r12), .mov .rcx (.reg .r14)]) <|
  .seq mulLoop <|
  .seq (.block [.mov .rdi (.reg .rbx), .mov .rsi (.reg .rdx), .mov .r8 (.reg .r13),
    .alu .add .r8 (.imm 192), .mov .rcx (.reg .r14), .shift .shr .rcx 3]) <|
  .seq xorLoop <|
  .seq (blockMixTo blockMix [.mov .rdi (.reg .r13), .alu .add .rdi (.imm 192)])
    (.block [.alu .sub .r15 (.imm 1)])

/-- Restoring our caller's registers. -/
def rmEpilogue : List Instr := rmSaved.map fun (r, d) => .mov r (.mem (at_ .r13 d))

def roMixWith (blockMix : Prog isa) : Prog isa :=
  .seq (.block rmPrologue) <|
  .seq nLoop <|
  .seq (.block rmSetup) <|
  .seq (.loop (step2 blockMix) .ne) <|
  .seq (.block rmMid) <|
  .seq (.loop (step3 blockMix) .ne)
    (.block rmEpilogue)

def roMix : Prog isa := roMixWith blockMix

end VG.Impl.Scrypt.X86_64
