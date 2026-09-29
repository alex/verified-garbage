import VerifiedGarbage.Impl.MlKem.AArch64.Ntt
import VerifiedGarbage.Impl.Sha3.AArch64.Stream

/-!
# ML-KEM on AArch64: `SampleNTT`

`sampleNTT(seed = x0, a = x1, scratch = x2) -> x0`: SHAKE128 of the 34
bytes at `seed`, by the verified `vg_keccak_absorb`, `vg_keccak_pad` and
`vg_keccak_squeeze` from the all-zero state, squeezing 840 bytes (the
`3 · 280` bytes of `minIterations = 280` iterations) at once; then the 280
iterations of the loop of Algorithm 7 on them, which stop accepting
coefficients once there are 256. Returns 1 if there are 256, and 0 if not.

`scratch` (2048 bytes) is laid out as:

* `[0, 840)`: the SHAKE128 output;
* `[840, 1040)`: the Keccak state;
* `[1040, 1680)`: the Keccak functions' working space;
* `[1680, 1704)`: our caller's `x25`, `x26` and `x30`, which we save there
  and restore before the loop.

The Keccak calls keep `x25` = `a` and `x26` = `scratch` (callee-saved) for
us. The loop keeps `x2` = the next chunk of output, `x3` = the next
coefficient of `a`, `x4` = the coefficients still to accept (`256 - j`),
`x5` = the iterations left, `x9` = `q` and `x10` = 15. Before it, `a` is set
to zeros, so that the loop only ever reads the output and writes `a`.

The loop's branches and the addresses it writes depend on the SHAKE128
output, and so on the seed, which the contract declares that it may leak;
everything else depends only on the pointers.
-/

namespace VG.Impl.MlKem.AArch64

open VG.AArch64

/-- Save `x25`, `x26` and `x30` in `scratch` (`x2`), keep `a` and `scratch`
in `x25` and `x26`, zero the Keccak state, and pass `absorb` its arguments:
the state, the rate 168, the position 0, the seed, its length 34, and the
working space. -/
def samplePrologue : List Instr :=
  [.str .x .x25 .x2 1680, .str .x .x26 .x2 1688, .str .x .x30 .x2 1696, mov .x25 .x1,
    mov .x26 .x2, .movz .x .x9 0 0] ++
  (List.range 25).map (fun k => .str .x .x9 .x2 (840 + 8 * k)) ++
  ([mov .x3 .x0, .addImm .x .x0 .x26 840, .movz .x .x1 168 0, .movz .x .x2 0 0, .movz .x .x4 34 0,
    .addImm .x .x5 .x26 1040] : List Instr)

/-- `pad`'s arguments: the state, the rate, the position 34, the SHAKE suffix
`0x1f`, and the working space. -/
def samplePadArgs : List Instr :=
  [.addImm .x .x0 .x26 840, .movz .x .x1 168 0, .movz .x .x2 34 0, .movz .x .x3 0x1f 0,
    .addImm .x .x4 .x26 1040]

/-- `squeeze`'s arguments: the state, the rate, the position 0, the output
at `scratch`, its length 840, and the working space. -/
def sampleSqueezeArgs : List Instr :=
  [.addImm .x .x0 .x26 840, .movz .x .x1 168 0, .movz .x .x2 0 0, mov .x3 .x26,
    .movz .x .x4 840 0, .addImm .x .x5 .x26 1040]

/-- One coefficient of `a` set to zero. -/
def zeroBody : List Instr := [.str .w .x9 .x3 0, .addImm .x .x3 .x3 4, .subImm .x .x4 .x4 1]

/-- Set `a` to zeros. -/
def sampleZero : Prog isa :=
  .seq (.block [.movz .x .x9 0 0, mov .x3 .x25, .movz .x .x4 256 0])
    (.loop (.block zeroBody) (.nonzero .x .x4))

/-- The loop's registers, and our caller's `x30`, `x25` and `x26` back. -/
def sampleSetup : List Instr :=
  [mov .x2 .x26, mov .x3 .x25, .movz .x .x4 256 0, .movz .x .x5 280 0, .movz .x .x9 3329 0,
    .movz .x .x10 15 0, .ldr .x .x30 .x26 1696, .ldr .x .x25 .x26 1680, .ldr .x .x26 .x26 1688]

/-- Everything before the loop. -/
def sampleSqueeze : Prog isa :=
  .seq (.block samplePrologue) <|
  .seq (.call "vg_keccak_absorb" Impl.Sha3.AArch64.Stream.absorb) <|
  .seq (.block samplePadArgs) <|
  .seq (.call "vg_keccak_pad" Impl.Sha3.AArch64.Stream.pad) <|
  .seq (.block sampleSqueezeArgs) <|
  .seq (.call "vg_keccak_squeeze" Impl.Sha3.AArch64.Stream.squeeze) <|
  .seq sampleZero (.block sampleSetup)

/-- Accept the candidate `d` if it is less than `q`: store it and count it. -/
def sampleAccept (d : Reg) : Prog isa :=
  .seq (.block [.sub .x .x13 d .x9, .lsr .x .x14 .x13 63])
    (.ite (.zero .x .x14) (.block [])
      (.block [.str .w d .x3 0, .addImm .x .x3 .x3 4, .subImm .x .x4 .x4 1]))

/-- The candidates `d₁` (`x11`) and `d₂` (`x12`) of the chunk at `x2`. -/
def sampleChunk : List Instr :=
  [.ldrb .x6 .x2 0, .ldrb .x7 .x2 1, .ldrb .x8 .x2 2, .addImm .x .x2 .x2 3, .subImm .x .x5 .x5 1,
    .logic .and .x .x11 .x7 .x10, .lsl .x .x11 .x11 8, .add .x .x11 .x11 .x6, .lsr .x .x12 .x7 4,
    .lsl .x .x13 .x8 4, .add .x .x12 .x12 .x13]

/-- One iteration: nothing once there are 256 coefficients. -/
def sampleBody : Prog isa :=
  .seq (.block sampleChunk)
    (.ite (.zero .x .x4) (.block [])
      (.seq (sampleAccept .x11) (.ite (.zero .x .x4) (.block []) (sampleAccept .x12))))

/-- The 280 iterations, then 1 if there are 256 coefficients (`x4 = 0`). -/
def sampleLoop : Prog isa :=
  .seq (.loop sampleBody (.nonzero .x .x5)) (.block [.subImm .x .x0 .x4 1, .lsr .x .x0 .x0 63])

def sampleNTT : Prog isa := .seq sampleSqueeze sampleLoop

end VG.Impl.MlKem.AArch64
