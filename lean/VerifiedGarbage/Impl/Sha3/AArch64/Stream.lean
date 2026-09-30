import VerifiedGarbage.Impl.Sha3.AArch64

/-!
# The SHA-3 sponge: AArch64 implementation

The same structure as the x86-64 implementation. The streaming state is the
Keccak state (`[u64; 25]` at `state`), with the bytes of a partial block
XORed into it as they arrive (see `VG.Spec.Sha3.Repr`); the position in the
block is kept by the caller.

* `absorb(state = x0, rate = x1, pos = x2, data = x3, len = x4,
  scratch = x5)` XORs the bytes of `data` into the state from byte `pos`, a
  lane (8 bytes) at a time where the position is at a lane and at least 8
  bytes are left, and a byte at a time otherwise, permuting the state
  whenever a block is complete, and returns the position after them.
* `pad(state = x0, rate = x1, pos = x2, suffix = x3, scratch = x4)` XORs
  the suffix into byte `pos` and `0x80` into byte `rate - 1`, and permutes
  the state.
* `squeeze(state = x0, rate = x1, pos = x2, out = x3, outlen = x4,
  scratch = x5)` copies the state to `out` from byte `pos`, a lane (8 bytes)
  at a time where the position is at a lane and at least 8 bytes are left
  (every rate is a whole number of lanes), and a byte at a time otherwise,
  permuting it whenever a block has been used up and more output is
  needed, and returns the position after them.

The permutation is called (`vg_keccak_f1600`, `Impl.Sha3.AArch64.permute`)
with the first 512 bytes of `scratch` as its scratch space. It uses only
`x0`–`x15`, and preserves `x19`–`x28`, so `absorb` and `squeeze` keep their
variables there (`x19` = `state`, `x20` = `scratch`), and save their
caller's values of those registers in `scratch[512..560)`. Our return
address (`x30`), which each call replaces, is saved in a stack frame around
the whole function.

The model has no register-offset addressing, so byte `pos` of the state is
addressed as `[x10]` with `x10 = state + pos` computed just before the
access. It has no flags either: the comparison of the position with the
rate is a subtraction tested with `cbz`. Every address and branch depends
only on the pointers, `rate`, `pos` and the lengths.
-/

namespace VG.Impl.Sha3.AArch64.Stream

open VG.AArch64
open VG.Impl.Sha3.AArch64 (mov permute)

/-- The callee-saved registers we use, and where they are saved in `scratch`. -/
def saved : List (Reg × Nat) :=
  [(.x19, 512), (.x20, 520), (.x21, 528), (.x22, 536), (.x23, 544), (.x24, 552)]

/-- Save them, with `scratch` in `b`. -/
def save (b : Reg) : List Instr := saved.map fun (r, d) => .str .x r b d

/-- Restore them from `scratch` in `x20` (`x20`, the base, last). -/
def restore : List Instr :=
  (saved.filter (·.1 != .x20)).map (fun (r, d) => .ldr .x r .x20 d) ++ [.ldr .x .x20 .x20 520]

/-- Permute the state at `x19`, with scratch space `x20`. -/
def permuteAt : Prog isa :=
  .seq (.block [mov .x0 .x19, mov .x1 .x20]) (.call "vg_keccak_f1600" permute)

/-- Registers: `x19` = `state`, `x20` = `scratch`, `x21` = `rate`, `x22` = the
position in the block, `x23` = `data` or `out`, `x24` = bytes of it left. -/
def setup : List Instr :=
  save .x5 ++ [mov .x19 .x0, mov .x20 .x5, mov .x21 .x1, mov .x22 .x2, mov .x23 .x3, mov .x24 .x4]

/-! ## `absorb` -/

/-- `x10 = 0` exactly when the position is at a lane (`x22 mod 8 = 0`) and at
least 8 bytes are left (of data or of output) (`x24 ≥ 8`, as `x24 - 8` is then non-negative). -/
def wordTest : List Instr :=
  [.movz .x .x10 7 0, .logic .and .x .x10 .x22 .x10, .subImm .x .x11 .x24 8, .lsr .x .x11 .x11 63,
    .logic .orr .x .x10 .x10 .x11]

/-- A lane of data XORed into the state; `x9 = 0` if that completes the block. -/
def absorbWord : List Instr :=
  [.ldr .x .x9 .x23 0, .add .x .x10 .x19 .x22, .ldr .x .x11 .x10 0, .logic .eor .x .x9 .x9 .x11,
    .str .x .x9 .x10 0, .addImm .x .x23 .x23 8, .addImm .x .x22 .x22 8, .subImm .x .x24 .x24 8,
    .sub .x .x9 .x22 .x21]

/-- A byte of data XORed into the state; `x9 = 0` if that completes the block. -/
def absorbByte : List Instr :=
  [.ldrb .x9 .x23 0, .add .x .x10 .x19 .x22, .ldrb .x11 .x10 0, .logic .eor .x .x9 .x9 .x11,
    .strb .x9 .x10 0, .addImm .x .x23 .x23 1, .addImm .x .x22 .x22 1, .subImm .x .x24 .x24 1,
    .sub .x .x9 .x22 .x21]

def absorbBody : Prog isa :=
  .seq (.block wordTest)
  (.seq (.ite (.zero .x .x10) (.block absorbWord) (.block absorbByte))
    (.ite (.zero .x .x9) (.seq (.block [.movz .x .x22 0 0]) permuteAt) (.block [])))

/-- `absorb`, but for saving `x30`. -/
def absorbMain : Prog isa :=
  .seq (.block setup)
  (.seq (.ite (.zero .x .x24) (.block []) (.loop absorbBody (.nonzero .x .x24)))
    (.block (mov .x0 .x22 :: restore)))

def absorb : Prog isa := .frame (.push .x30) absorbMain (.pop .x30)

/-! ## `pad` -/

/-- `pad`, but for saving `x30`. -/
def padMain : Prog isa :=
  .seq (.block [.add .x .x9 .x0 .x2, .ldrb .x10 .x9 0, .logic .eor .x .x10 .x10 .x3,
      .strb .x10 .x9 0, .add .x .x9 .x0 .x1, .subImm .x .x9 .x9 1, .ldrb .x10 .x9 0,
      .movz .x .x11 0x80 0, .logic .eor .x .x10 .x10 .x11, .strb .x10 .x9 0, mov .x1 .x4])
    (.call "vg_keccak_f1600" permute)

def pad : Prog isa := .frame (.push .x30) padMain (.pop .x30)

/-! ## `squeeze` -/

/-- A lane of the state to `out`. -/
def squeezeWord : List Instr :=
  [.add .x .x10 .x19 .x22, .ldr .x .x9 .x10 0, .str .x .x9 .x23 0, .addImm .x .x23 .x23 8,
    .addImm .x .x22 .x22 8, .subImm .x .x24 .x24 8]

/-- A byte of the state to `out`. -/
def squeezeByte : List Instr :=
  [.add .x .x10 .x19 .x22, .ldrb .x9 .x10 0, .strb .x9 .x23 0, .addImm .x .x23 .x23 1,
    .addImm .x .x22 .x22 1, .subImm .x .x24 .x24 1]

def squeezeBody : Prog isa :=
  .seq (.block [.sub .x .x9 .x22 .x21])
  (.seq (.ite (.zero .x .x9) (.seq (.block [.movz .x .x22 0 0]) permuteAt) (.block []))
    (.seq (.block wordTest) (.ite (.zero .x .x10) (.block squeezeWord) (.block squeezeByte))))

/-- `squeeze`, but for saving `x30`. -/
def squeezeMain : Prog isa :=
  .seq (.block setup)
  (.seq (.ite (.zero .x .x24) (.block []) (.loop squeezeBody (.nonzero .x .x24)))
    (.block (mov .x0 .x22 :: restore)))

def squeeze : Prog isa := .frame (.push .x30) squeezeMain (.pop .x30)

end VG.Impl.Sha3.AArch64.Stream
