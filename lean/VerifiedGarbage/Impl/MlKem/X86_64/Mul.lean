import VerifiedGarbage.Impl.MlKem.X86_64.Common
import VerifiedGarbage.Spec.MlKem

/-!
# ML-KEM on x86-64: `vg_mlkem_multiply_ntts`

`multiplyNTTs(h = rdi, f = rsi, g = rdx, scratch = rcx)`: the prologue
stores the 128 moduli `γᵢ = ζ^(2 BitRev7(i) + 1) mod q` to `scratch` as
`u32`s (immediates: the code has no other memory). Then, with `rsi`, `r8`
(`g`) and `rdi` pointing at the pair `i` of `f`, `g` and `h`, `r9` at `γᵢ`
and `rcx` counting down, each pair is

* `h[2i] = (a₁b₁ mod q) · γᵢ + a₀b₀`, reduced, and
* `h[2i + 1] = a₀b₁ + a₁b₀`, reduced,

each sum less than `2q² < 2³²`, reduced with `reduce` (a Barrett reduction
with `mul`). Every address and branch depends only on the pointers.
-/

namespace VG.Impl.MlKem.X86_64

open VG.X86_64

/-- `γᵢ = ζ^(2 BitRev7(i) + 1) mod q`. -/
def gammaTab (i : Nat) : Nat := 17 ^ (2 * Spec.MlKem.bitRev7 i + 1) % 3329

/-- The even coefficient of the pair. -/
def mulEven : List Instr :=
  [.mov32 .rax (.mem (at_ .rsi 4)), .mov32 .rdx (.mem (at_ .r8 4)), .mul .rdx] ++ reduce ++
    [.mov32 .rax (.mem (at_ .r9 0)), .mul .r10, .mov .r11 (.reg .rax), .mov32 .rax (.mem (at_ .rsi 0)),
      .mov32 .rdx (.mem (at_ .r8 0)), .mul .rdx, .alu .add .rax (.reg .r11)] ++ reduce ++
    [.store32 (at_ .rdi 0) .r10]

/-- The odd coefficient of the pair. -/
def mulOdd : List Instr :=
  [.mov32 .rax (.mem (at_ .rsi 0)), .mov32 .rdx (.mem (at_ .r8 4)), .mul .rdx, .mov .r11 (.reg .rax),
    .mov32 .rax (.mem (at_ .rsi 4)), .mov32 .rdx (.mem (at_ .r8 0)), .mul .rdx, .alu .add .rax (.reg .r11)] ++
    reduce ++ [.store32 (at_ .rdi 4) .r10]

def mulStep : List Instr :=
  [.alu .add .rdi (.imm 8), .alu .add .rsi (.imm 8), .alu .add .r8 (.imm 8), .alu .add .r9 (.imm 4),
    .alu .sub .rcx (.imm 1)]

def mulBody : List Instr := mulEven ++ mulOdd ++ mulStep

def multiplyNTTs : Prog isa :=
  .seq (.block ([.mov .r8 (.reg .rdx), .mov .r9 (.reg .rcx)] ++ storeTab gammaTab 128))
    (.seq (.block [.mov32 .rcx (.imm 128)]) (.loop (.block mulBody) .ne))

end VG.Impl.MlKem.X86_64
