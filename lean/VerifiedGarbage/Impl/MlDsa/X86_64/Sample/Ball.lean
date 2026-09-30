import VerifiedGarbage.Impl.MlDsa.X86_64.Sample.Common

/-!
# ML-DSA on x86-64: `vg_mldsa_sample_in_ball`

`sampleInBall(ctilde = rdi, len = rsi, tau = edx, c = rcx, scratch = r8) ->
eax` (see `Common.lean` for the layout) squeezes 272 bytes of SHAKE256 of the
`len` bytes of `c̃` (2 blocks; the least bound of FIPS 204 Appendix C is 221
bytes, the contract's largest 1088), zeroes `c`, and runs `SampleInBall`'s
loop over the 264 bytes after the first 8, with `rsi` at the byte, `rdi` =
`i` (from `256 - τ`), `r9` the sign bits not yet used (the first 8 bytes, as
a `u64`, shifted right once per coefficient set) and `rcx` counting down:
while `i < 256`, a byte `j ≤ i` sets `c[i] ← c[j]` and `c[j] ← ±1` (1, or
`q - 1` if the next sign bit is 1), and increments `i`. It returns
`i >> 8`: 1 if `i = 256`, and 0 otherwise.

Its branches and addresses depend on the SHAKE256 output, a function of
`c̃`, which the contract lets it leak.
-/

namespace VG.Impl.MlDsa.X86_64.Sample

open VG.X86_64
open VG.Impl.MlKem.X86_64 (at_)

/-- `c[rax]`: `[rbp + 4 rax]`. -/
def cJ : MemOp := { base := .rbp, index := some .rax, scale := 4 }

/-- The 256 coefficients of `c` zeroed. -/
def bZero : Prog isa :=
  .seq (.block [.mov32 .rax (.imm 0), .mov .rdi (.reg .rbp)])
    (.seq (.block [.mov32 .rcx (.imm 256)])
      (.loop (.block [.store32 (at_ .rdi 0) .rax, .alu .add .rdi (.imm 4), .alu .sub .rcx (.imm 1)]) .ne))

/-- The sign bits in `r9`, `i = 256 - τ`, and `rsi` at the byte after them. -/
def bSetup : List Instr :=
  [.mov .r9 (.mem (at_ .rbx 840)), .mov32 .rdi (.imm 256), .alu32 .sub .rdi (.reg .r12), .mov .rsi (.reg .rbx),
    .alu .add .rsi (.imm 848)]

/-- `c[i] ← c[j]`, `c[j] ← ±1`, the sign bits shifted, `i` incremented. -/
def bSet : Prog isa :=
  .seq (.block [.mov32 .rdx (.mem cJ), .store32 aJ .rdx, .alu .test .r9 (.imm 1)])
    (.seq (.ite .e (.block [.mov32 .rdx (.imm 1)]) (.block [.mov32 .rdx (.imm (qImm - 1))]))
      (.block [.store32 cJ .rdx, .shift .shr .r9 1, .alu .add .rdi (.imm 1)]))

/-- The byte `j` at `rsi`, rejected if `i < j`. -/
def bTry : Prog isa :=
  .seq (.block [.movzx8 .rax (at_ .rsi 0), .alu .cmp .rdi (.reg .rax)]) (.ite .b (.block []) bSet)

def bBody : Prog isa :=
  .seq (.block [.alu .cmp .rdi (.imm 256)])
    (.seq (.ite .b bTry (.block [])) (.block [.alu .add .rsi (.imm 1), .alu .sub .rcx (.imm 1)]))

def bLoop : Prog isa :=
  .seq (.block bSetup) (.seq (.block [.mov32 .rcx (.imm 264)]) (.loop bBody .ne))

def sampleInBall : Prog isa :=
  .seq (.block (pro .r8 .rcx (.reg .rdx) (.reg .rsi)))
    (.seq (sponge 136 272) (.seq bZero (.seq bLoop (.block (retJ ++ epi)))))

end VG.Impl.MlDsa.X86_64.Sample
