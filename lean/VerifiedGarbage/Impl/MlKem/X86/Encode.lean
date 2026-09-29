import VerifiedGarbage.Impl.MlKem.X86.Basic

/-!
# ML-KEM on x86 (32-bit): `vg_mlkem_encode12` and `vg_mlkem_decode12`

Both are leaves (`leaf`) looping over the 128 pairs of coefficients, each
three bytes of the encoding, with `esi` at the input, `edi` at the output
and `ecx` the pairs left. The model has no left shift: a value `v < 2ⁿ`
rotated right by `n` is `v` shifted left by `32 - n` (`ror`).

* `encode12(f, out)`: the pair `f₀, f₁` is the 24-bit number
  `w = f₀ + 2¹² f₁`, stored a byte at a time.
* `decode12(b, f)`: the three bytes of a pair are loaded into `eax`, `ebx`
  and `edx`; `f₁ = ⌊b₁ / 16⌋ + 2⁴ b₂` is computed in `ebp` and
  `f₀ = b₀ + 2⁸ (b₁ mod 16)` in `eax`, each less than `2¹² < 2q`, and
  reduced with `csub`.

Every address and branch depends only on the pointers.
-/

namespace VG.Impl.MlKem.X86

open VG.X86

/-- `++`, grouping to the right. -/
local infixr:65 " +++ " => HAppend.hAppend

/-! ## `encode12` -/

def enc12Body : List Instr :=
  [.mov .eax (.mem (at_ .esi 0)), .mov .edx (.mem (at_ .esi 4)), .shift .ror .edx 20,
    .alu .add .eax (.reg .edx), .store8 (at_ .edi 0) .al, .shift .shr .eax 8,
    .store8 (at_ .edi 1) .al, .shift .shr .eax 8, .store8 (at_ .edi 2) .al,
    .alu .add .esi (.imm 8), .alu .add .edi (.imm 3), .alu .sub .ecx (.imm 1)]

/-- `esi = f`, `edi = out`, `ecx = 128`. -/
def enc12Init : List Instr :=
  [.mov .esi (.mem (at_ .esp 20)), .mov .edi (.mem (at_ .esp 24)), .mov .ecx (.imm 128)]

def encode12 : Prog isa := leaf (.seq (.block enc12Init) (.loop (.block enc12Body) .ne))

/-! ## `decode12` -/

def dec12Body : List Instr :=
  [.movzx8 .eax (at_ .esi 0), .movzx8 .ebx (at_ .esi 1), .movzx8 .edx (at_ .esi 2),
    .mov .ebp (.reg .ebx), .shift .shr .ebp 4, .shift .ror .edx 28, .alu .add .ebp (.reg .edx),
    .alu .and .ebx (.imm 15), .shift .ror .ebx 24, .alu .add .eax (.reg .ebx)] +++ csub .eax .edx +++
  .store (at_ .edi 0) .eax :: csub .ebp .edx +++
  [.store (at_ .edi 4) .ebp, .alu .add .esi (.imm 3), .alu .add .edi (.imm 8),
    .alu .sub .ecx (.imm 1)]

/-- `esi = b`, `edi = f`, `ecx = 128`. -/
def dec12Init : List Instr := enc12Init

def decode12 : Prog isa := leaf (.seq (.block dec12Init) (.loop (.block dec12Body) .ne))

end VG.Impl.MlKem.X86
