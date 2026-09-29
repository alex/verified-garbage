import VerifiedGarbage.Impl.Scrypt.X86.Salsa

/-!
# scryptBlockMix: x86 (32-bit) implementation

`blockmix(b = [esp + 4], r = [esp + 8], y = [esp + 12], ry = [esp + 16],
scratch = [esp + 20])`, every argument on the stack (cdecl), writes
scryptBlockMix (RFC 7914 §4) of the `128 * r` bytes at `b` to the `128 * r`
bytes at `y`.

As on the other targets (`Impl/Scrypt/Arm/BlockMix.lean`), step 2's `Y[i]`
go straight to their places in step 3's output: `Y[2k]` to `y + 64k` and
`Y[2k + 1]` to `y + 64 (r + k)`. Each is computed in place: `T = X xor B[i]`
is written there, and `vg_salsa20_8` replaces it by `Salsa (T)`. `X` is then
the block just written (initially `B[2r - 1]`). The loop runs once for each
pair `(2k, 2k + 1)`.

`vg_salsa20_8` preserves `ebx`, `esi`, `edi` and `ebp`, so our variables live
there across it: `ebx` is `B[2k]`, `esi` is `y + 64k`, `edi` is
`y + 64 (r + k)` and `ebp` is `X`. The loop ends when `esi` reaches
`y + 64 r`, computed from the arguments (`64 r` with `mul`). `scratch`
(128 bytes) holds Salsa20/8's working space (`[0, 64)`) and our caller's
`ebx`, `esi`, `edi` and `ebp` (`[64, 80)`). Each call of `vg_salsa20_8`
pushes its two arguments in a frame of its own, popped (into `eax`) when it
returns: with the return address the call stores, it uses the 12 bytes
below `esp`. Every address is `esp` or one of our variables plus a constant,
and the only branch is on the pointers and `r`, so only they affect timing.
-/

namespace VG.Impl.Scrypt.X86

open VG.X86

/-- The callee-saved registers, and where they are saved in `scratch`. -/
def bmSaved : List (Reg × Nat) := [(.ebx, 64), (.esi, 68), (.edi, 72), (.ebp, 76)]

/-- Word `k` of `[dst] ← [x] xor [src]`. -/
def xorW (dst x src : Reg) (k : Nat) : List Instr :=
  [.mov .eax (.mem (at_ x (4 * k))), .alu .xor .eax (.mem (at_ src (4 * k))),
    .store (at_ dst (4 * k)) .eax]

/-- The 64 bytes `[dst] ← [x] xor [src]`. -/
def xor64 (dst x src : Reg) : List Instr := (List.range 16).flatMap (xorW dst x src)

/-- `vg_salsa20_8(dst, scratch)`, its arguments pushed last to first. -/
def salsaAt (salsa : Prog isa) (dst : Reg) : Prog isa :=
  .seq (.block [.mov .eax (.mem (at_ .esp 20))])
    (.frame (.push [.eax, dst]) (.call "vg_salsa20_8" salsa) (.pop .eax 2))

/-- `eax ← m r`, from the argument `r` at `[esp + 8]` (`ecx = m`, `edx` the
high half of the product). -/
def timesR (m : BitVec 32) : List Instr := [.mov .eax (.mem (at_ .esp 8)), .mov .ecx (.imm m), .mul .ecx]

/-- Saving our caller's registers and setting up ours: `ebx = b`, `esi = y`,
`edi = y + 64 r`, `ebp = b + 128 r - 64` (`B[2r - 1]`). -/
def bmPrologue : List Instr :=
  .mov .eax (.mem (at_ .esp 20)) :: bmSaved.map (fun (r, d) => .store (at_ .eax d) r) ++
    [.mov .ebx (.mem (at_ .esp 4)), .mov .esi (.mem (at_ .esp 12))] ++ timesR 64 ++
    [.mov .edi (.reg .esi), .alu .add .edi (.reg .eax), .mov .ebp (.reg .ebx), .alu .add .ebp (.reg .eax),
     .alu .add .ebp (.reg .eax), .alu .sub .ebp (.imm 64)]

/-- The end of a pair: the pointers move on, and `esi` is compared with
`y + 64 r`. -/
def bmNext : List Instr :=
  [.mov .ebp (.reg .edi), .alu .add .ebx (.imm 64), .alu .add .esi (.imm 64), .alu .add .edi (.imm 64)] ++
    timesR 64 ++ [.mov .ecx (.mem (at_ .esp 12)), .alu .add .eax (.reg .ecx), .alu .cmp .esi (.reg .eax)]

/-- One pair: `Y[2k]` from `X` and `B[2k]`, then `Y[2k + 1]` from it and
`B[2k + 1]`; then the pointers move on. -/
def bmBody (salsa : Prog isa) : Prog isa :=
  .seq (.block (xor64 .esi .ebp .ebx)) <|
  .seq (salsaAt salsa .esi) <|
  .seq (.block (.alu .add .ebx (.imm 64) :: xor64 .edi .esi .ebx)) <|
  .seq (salsaAt salsa .edi)
    (.block bmNext)

/-- Restoring our caller's registers. -/
def bmEpilogue : List Instr :=
  .mov .eax (.mem (at_ .esp 20)) :: bmSaved.map fun (r, d) => .mov r (.mem (at_ .eax d))

def blockMixWith (salsa : Prog isa) : Prog isa :=
  .seq (.block bmPrologue) (.seq (.loop (bmBody salsa) .ne) (.block bmEpilogue))

def blockMix : Prog isa := blockMixWith salsa

end VG.Impl.Scrypt.X86
