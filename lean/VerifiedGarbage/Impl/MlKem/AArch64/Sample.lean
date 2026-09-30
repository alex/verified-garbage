import VerifiedGarbage.Impl.MlKem.AArch64.Ntt
import VerifiedGarbage.Impl.Sha3.AArch64.Stream

/-!
# ML-KEM on AArch64: `SampleNTT`

`sampleNTT(seed = x0, a = x1, scratch = x2) -> x0`: SHAKE128 of the 34
bytes at `seed`, by the verified `vg_keccak_absorb`, `vg_keccak_pad` and
`vg_keccak_squeeze` from the all-zero state, and the iterations of the loop
of Algorithm 7 on its output, which stop accepting coefficients once there
are 256. Returns 1 if there are 256 within `minIterations = 280` iterations,
and 0 if not.

Three blocks of output (504 bytes, for 168 iterations) almost always give
256 coefficients, so the output is squeezed in two tries:

* `sampleFast`: the first 504 bytes, and 168 iterations on them;
* if they leave fewer than 256 coefficients, `sampleFull`, from the start
  again: 840 bytes (the `3 · 280` of 280 iterations), squeezed at once, and
  the 280 iterations on them.

`scratch` (2048 bytes) is laid out as:

* `[0, 840)`: the SHAKE128 output;
* `[840, 1040)`: the Keccak state;
* `[1040, 1680)`: the Keccak functions' working space;
* `[1680, 1712)`: our caller's `x25`, `x26`, `x30` and `x24`, which each
  try saves there, and restores before its loop (`sampleFull`) or after it
  (`sampleFast`).

The Keccak calls keep `x24` = `seed`, `x25` = `a` and `x26` = `scratch`
(callee-saved) for us. The loop keeps `x2` = the next chunk of output,
`x3` = the next coefficient of `a`, `x4` = the coefficients still to accept
(`256 - j`), `x5` = the iterations left, `x9` = `q` and `x10` = 15. Before
it, `a` is set to zeros, so that the loop only ever reads the output and
writes `a`. The loop stores each candidate as coefficient `j`, and moves on
only if it accepts it: until there are 256, coefficient `j` may hold a
rejected candidate, which `sampleLoop` sets back to zero if the loop ends
with fewer.

The loop's branches, the addresses it writes, and whether `sampleFull`
runs depend on the SHAKE128 output, and so on the seed, which the contract
declares that it may leak; everything else depends only on the pointers.
-/

namespace VG.Impl.MlKem.AArch64

open VG.AArch64

/-- Save `x25`, `x26`, `x30` and `x24` in `scratch` (`x2`), keep `seed`, `a`
and `scratch` in `x24`, `x25` and `x26`, zero the Keccak state, and pass
`absorb` its arguments: the state, the rate 168, the position 0, the seed,
its length 34, and the working space. -/
def samplePrologue : List Instr :=
  [.str .x .x25 .x2 1680, .str .x .x26 .x2 1688, .str .x .x30 .x2 1696, .str .x .x24 .x2 1704,
    mov .x24 .x0, mov .x25 .x1, mov .x26 .x2, .movz .x .x9 0 0] ++
  (List.range 25).map (fun k => .str .x .x9 .x2 (840 + 8 * k)) ++
  ([mov .x3 .x0, .addImm .x .x0 .x26 840, .movz .x .x1 168 0, .movz .x .x2 0 0, .movz .x .x4 34 0,
    .addImm .x .x5 .x26 1040] : List Instr)

/-- `pad`'s arguments: the state, the rate, the position 34, the SHAKE suffix
`0x1f`, and the working space. -/
def samplePadArgs : List Instr :=
  [.addImm .x .x0 .x26 840, .movz .x .x1 168 0, .movz .x .x2 34 0, .movz .x .x3 0x1f 0,
    .addImm .x .x4 .x26 1040]

/-- `squeeze`'s arguments: the state, the rate 168, the position 0, the output
at `scratch`, its length `len`, and the working space. -/
def sampleSqueezeArgs (len : Nat) : List Instr :=
  [.addImm .x .x0 .x26 840, .movz .x .x1 168 0, .movz .x .x2 0 0, mov .x3 .x26,
    .movz .x .x4 (BitVec.ofNat 16 len) 0, .addImm .x .x5 .x26 1040]

/-- One coefficient of `a` set to zero. -/
def zeroBody : List Instr := [.str .w .x9 .x3 0, .addImm .x .x3 .x3 4, .subImm .x .x4 .x4 1]

/-- Set `a` to zeros. -/
def sampleZero : Prog isa :=
  .seq (.block [.movz .x .x9 0 0, mov .x3 .x25, .movz .x .x4 256 0])
    (.loop (.block zeroBody) (.nonzero .x .x4))

/-- The loop's registers for `iters` iterations. -/
def sampleRegs (iters : Nat) : List Instr :=
  [mov .x2 .x26, mov .x3 .x25, .movz .x .x4 256 0, .movz .x .x5 (BitVec.ofNat 16 iters) 0,
    .movz .x .x9 3329 0, .movz .x .x10 15 0]

/-- Our caller's `x30`, `x24`, `x25` and `x26` back. -/
def sampleRestore : List Instr :=
  [.ldr .x .x30 .x26 1696, .ldr .x .x24 .x26 1704, .ldr .x .x25 .x26 1680, .ldr .x .x26 .x26 1688]

/-- The loop's registers for 280 iterations, and our caller's registers
back. -/
def sampleSetup : List Instr := sampleRegs 280 ++ sampleRestore

/-- Everything before the loop, squeezing `len` bytes, and `setup`. -/
def sampleSqueezeN (len : Nat) (setup : List Instr) : Prog isa :=
  .seq (.block samplePrologue) <|
  .seq (.call "vg_keccak_absorb" Impl.Sha3.AArch64.Stream.absorb) <|
  .seq (.block samplePadArgs) <|
  .seq (.call "vg_keccak_pad" Impl.Sha3.AArch64.Stream.pad) <|
  .seq (.block (sampleSqueezeArgs len)) <|
  .seq (.call "vg_keccak_squeeze" Impl.Sha3.AArch64.Stream.squeeze) <|
  .seq sampleZero (.block setup)

/-- Everything before the loop of `sampleFull`. -/
def sampleSqueeze : Prog isa := sampleSqueezeN 840 sampleSetup

/-- Accept the candidate `d` if it is less than `q`, without a branch: store
it as the next coefficient either way, and count it (`x14`) only if it is
accepted, so that a rejected one is overwritten by the next. -/
def sampleAccept (d : Reg) : List Instr :=
  [.sub .x .x13 d .x9, .lsr .x .x14 .x13 63, .str .w d .x3 0, .lsl .x .x15 .x14 2,
    .add .x .x3 .x3 .x15, .sub .x .x4 .x4 .x14]

/-- The candidates `d₁` (`x11`) and `d₂` (`x12`) of the chunk at `x2`. -/
def sampleChunk : List Instr :=
  [.ldrb .x6 .x2 0, .ldrb .x7 .x2 1, .ldrb .x8 .x2 2, .addImm .x .x2 .x2 3, .subImm .x .x5 .x5 1,
    .logic .and .x .x11 .x7 .x10, .lsl .x .x11 .x11 8, .add .x .x11 .x11 .x6, .lsr .x .x12 .x7 4,
    .lsl .x .x13 .x8 4, .add .x .x12 .x12 .x13]

/-- One iteration: nothing once there are 256 coefficients. -/
def sampleBody : Prog isa :=
  .seq (.block sampleChunk)
    (.ite (.zero .x .x4) (.block [])
      (.seq (.block (sampleAccept .x11)) (.ite (.zero .x .x4) (.block [])
        (.block (sampleAccept .x12)))))

/-- The 280 iterations, then 1 if there are 256 coefficients (`x4 = 0`), or
0 and coefficient `j` (which may hold a rejected candidate) set to zero. -/
def sampleLoop : Prog isa :=
  .seq (.loop sampleBody (.nonzero .x .x5)) <|
  .seq (.ite (.zero .x .x4) (.block []) (.block [.movz .x .x13 0 0, .str .w .x13 .x3 0]))
    (.block [.subImm .x .x0 .x4 1, .lsr .x .x0 .x0 63])

/-- 840 bytes of output, and 280 iterations on them. -/
def sampleFull : Prog isa := .seq sampleSqueeze sampleLoop

/-- 504 bytes of output, and 168 iterations on them; our caller's registers
stay saved. -/
def sampleFast : Prog isa :=
  .seq (sampleSqueezeN 504 (sampleRegs 168)) (.loop sampleBody (.nonzero .x .x5))

/-- `sampleFull`'s arguments, from `x24`, `x25` and `x26`, and our caller's
registers back. -/
def sampleRetry : List Instr := [mov .x0 .x24, mov .x1 .x25, mov .x2 .x26] ++ sampleRestore

/-- 1 (there are 256 coefficients), and our caller's registers back. -/
def sampleDone : List Instr := .movz .x .x0 1 0 :: sampleRestore

def sampleNTT : Prog isa :=
  .seq sampleFast (.ite (.zero .x .x4) (.block sampleDone) (.seq (.block sampleRetry) sampleFull))

end VG.Impl.MlKem.AArch64
