import VerifiedGarbage.Impl.MlDsa.X86.Sample.Common

/-!
# ML-DSA on x86 (32-bit): `vg_mldsa_sample_in_ball`

`sampleInBall(ctilde, len, tau, c, scratch) -> eax` (see `Common.lean` for
the layout) squeezes 272 bytes of SHAKE256 of the `len` bytes of `c̃` (2
blocks; the least bound of FIPS 204 Appendix C is 221 bytes, the contract's
largest 1088), zeroes `c`, and runs `SampleInBall`'s loop over the 264 bytes
after the first 8, with `esi` at the byte, `edi` = `i` (from `256 - τ`),
`ebp` = `c` and `ecx` counting down: while `i < 256`, a byte `j ≤ i` sets
`c[i] ← c[j]` and `c[j] ← ±1` (1, or `q - 1` if the next sign bit is 1),
and increments `i`. The sign bits not yet used (the first 8 bytes, as a
64-bit number shifted right once per coefficient set) are kept in the
argument slots of `len` and `tau` on the stack (low word first), which the
contract lets it overwrite. It returns `i >> 8`: 1 if `i = 256`, and 0
otherwise.

Its branches and addresses depend on the SHAKE256 output, a function of
`c̃`, which the contract lets it leak.
-/

namespace VG.Impl.MlDsa.X86.Sample

open VG.X86
open VG.Impl.MlKem.X86 (at_ leaf)

/-- The 256 coefficients of `c` zeroed, with `ebp` = `c`. -/
def bZero : Prog isa :=
  .seq (.block [.mov .ebp (.mem (argOp 3)), .mov .eax (.imm 0), .mov .edi (.reg .ebp), .mov .ecx (.imm 256)])
    (.loop (.block [.store (at_ .edi 0) .eax, .alu .add .edi (.imm 4), .alu .sub .ecx (.imm 1)]) .ne)

/-- `i = 256 - τ`, the sign bits to the argument slots 1 and 2, `esi` at the
byte after them, and `ecx = 264`. -/
def bSetup : List Instr :=
  [.mov .edi (.imm 256), .alu .sub .edi (.mem (argOp 2)), .mov .eax (.mem (at_ .esi outOff)),
    .store (argOp 1) .eax, .mov .eax (.mem (at_ .esi (outOff + 4))), .store (argOp 2) .eax,
    .alu .add .esi (.imm (BitVec.ofNat 32 (outOff + 8))), .mov .ecx (.imm 264)]

/-- `eax = c + 4j`, `edx = c + 4i`, `c[i] ← c[j]`, and the next sign bit
tested. -/
def bMove : List Instr :=
  [.alu .add .eax (.reg .eax), .alu .add .eax (.reg .eax), .alu .add .eax (.reg .ebp), .mov .edx (.reg .edi),
    .alu .add .edx (.reg .edx), .alu .add .edx (.reg .edx), .alu .add .edx (.reg .ebp),
    .mov .ebx (.mem (at_ .eax 0)), .store (at_ .edx 0) .ebx, .mov .ebx (.mem (argOp 1)), .alu .test .ebx (.imm 1)]

/-- `c[j] ← ±1` (in `edx`), the sign bits shifted right by one, `i`
incremented. -/
def bShift : List Instr :=
  [.store (at_ .eax 0) .edx, .shift .shr .ebx 1, .mov .edx (.mem (argOp 2)), .alu .and .edx (.imm 1),
    .shift .ror .edx 1, .alu .add .ebx (.reg .edx), .store (argOp 1) .ebx, .mov .ebx (.mem (argOp 2)),
    .shift .shr .ebx 1, .store (argOp 2) .ebx, .alu .add .edi (.imm 1)]

/-- The byte `j` in `eax` taken: `c[i] ← c[j]`, `c[j] ← ±1`. -/
def bSet : Prog isa :=
  .seq (.block bMove)
    (.seq (.ite .e (.block [.mov .edx (.imm 1)]) (.block [.mov .edx (.imm (qImm - 1))])) (.block bShift))

/-- The byte `j` at `esi`, rejected if `i < j`. -/
def bTry : Prog isa :=
  .seq (.block [.movzx8 .eax (at_ .esi 0), .alu .cmp .edi (.reg .eax)]) (.ite .b (.block []) bSet)

def bBody : Prog isa :=
  .seq (.block [.alu .cmp .edi (.imm 256)])
    (.seq (.ite .b bTry (.block [])) (.block [.alu .add .esi (.imm 1), .alu .sub .ecx (.imm 1)]))

def sampleInBall : Prog isa :=
  leaf <|
  .seq (sponge 4 136 (.mem (argOp 1)) 272) <|
  .seq bZero <|
  .seq (.block bSetup) <|
  .seq (.loop bBody .ne) (.block (retJ .edi))

end VG.Impl.MlDsa.X86.Sample
