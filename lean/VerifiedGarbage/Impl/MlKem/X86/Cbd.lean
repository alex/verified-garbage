import VerifiedGarbage.Impl.MlKem.X86.Basic

/-!
# ML-KEM on x86 (32-bit): `vg_mlkem_cbd2`

A leaf (`leaf`) looping over the 128 bytes of `b`, each two coefficients:
one from its low nibble and one from its high nibble, with `esi` at the
byte (loaded into `ebx`), `edi` at the coefficients and `ecx` the bytes
left. For a nibble `v`
in `eax` (whose bits above 3 are ignored), `t = (v & 5) + ((v >> 1) & 5)`
holds `x = v₀ + v₁` in bits 0–1 and `y = v₂ + v₃` in bits 2–3
(`cbdNibble`), and the coefficient is `x + q - y` reduced with `csub`. Every
address and branch depends only on the pointers.
-/

namespace VG.Impl.MlKem.X86

open VG.X86

/-- `++`, grouping to the right. -/
local infixr:65 " +++ " => HAppend.hAppend

/-- `eax ← (x + q - y) mod q` for the nibble in `eax`, with `edx` as a temporary. -/
def cbdNibble : List Instr :=
  [.mov .edx (.reg .eax), .shift .shr .edx 1, .alu .and .eax (.imm 5), .alu .and .edx (.imm 5),
    .alu .add .eax (.reg .edx), .mov .edx (.reg .eax), .shift .shr .edx 2, .alu .and .eax (.imm 3),
    .alu .add .eax (.imm Q), .alu .sub .eax (.reg .edx)] +++ csub .eax .edx

def cbdBody : List Instr :=
  .movzx8 .ebx (at_ .esi 0) :: .mov .eax (.reg .ebx) :: cbdNibble +++ .store (at_ .edi 0) .eax ::
    .mov .eax (.reg .ebx) :: .shift .shr .eax 4 :: cbdNibble +++
  [.store (at_ .edi 4) .eax, .alu .add .esi (.imm 1), .alu .add .edi (.imm 8), .alu .sub .ecx (.imm 1)]

/-- `esi = b`, `edi = f`, `ecx = 128`. -/
def cbdInit : List Instr :=
  [.mov .esi (.mem (at_ .esp 20)), .mov .edi (.mem (at_ .esp 24)), .mov .ecx (.imm 128)]

def cbd2 : Prog isa := leaf (.seq (.block cbdInit) (.loop (.block cbdBody) .ne))

end VG.Impl.MlKem.X86
