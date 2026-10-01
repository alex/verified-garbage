import VerifiedGarbage.Impl.X25519.Arm

/-! Ed25519 field arithmetic on ARMv7 uses sixteen 16-bit limbs and only
32-bit `mul`. The multiplication accumulator follows the 22 field slots;
packed point tables let the complete implementation fit the reviewed 8 KiB
scratch contract. No long-multiply instructions are used. -/
namespace VG.Impl.Ed25519.Arm
open VG VG.Arm

abbrev carryStep := Impl.X25519.Arm.carryStep
abbrev pass := Impl.X25519.Arm.pass
abbrev ldSrc := Impl.X25519.Arm.ldSrc
abbrev tail := Impl.X25519.Arm.tail
abbrev prologue := Impl.X25519.Arm.prologue
abbrev addSrc := Impl.X25519.Arm.addSrc
abbrev add := Impl.X25519.Arm.add
abbrev subHi := Impl.X25519.Arm.subHi
abbrev subLo := Impl.X25519.Arm.subLo
abbrev subSrc := Impl.X25519.Arm.subSrc
abbrev sub := Impl.X25519.Arm.sub
abbrev storeN := Impl.X25519.Arm.storeN
abbrev cswapStep := Impl.X25519.Arm.cswapStep
abbrev cswap := Impl.X25519.Arm.cswap

def ACC : Nat := 1472

/-- The words `ACC[0, 16)` zeroed. -/
def zeroAcc : List Instr := .mov .r3 (.imm 0) :: storeN .r3 ACC 16

/-- Limb `j` of row `i` (`r7` = the base plus `4 i`, `a_i` in `r1`) into
`r3`: `a_i b_j + ACC[i + j]`. -/
def rowSrc (b j : Nat) : List Instr :=
  [.ldr .r2 .r0 (b + 4 * j), .mul .r2 .r1 .r2, .ldr .r3 .r7 (ACC + 4 * j), .dp .add .r3 .r3 (.reg .r2)]

/-- Row `i` of the product: `ACC[i, i + 17) = ACC[i, i + 16) + a_i · b`. -/
def row (a b : Nat) : List Instr :=
  [.ldr .r1 .r7 a, .mov .r5 (.imm 0)] ++ pass .r7 ACC (rowSrc b) ++
    [.str .r5 .r7 (ACC + 64), .dp .add .r7 .r7 (.imm 4), .subs .r9 .r9 (.imm 1)]

/-- Limb `k` of `lo + 38 hi` for the product in `ACC`, into `r3`. -/
def mulSrc (k : Nat) : List Instr :=
  [.ldr .r3 .r0 (ACC + 4 * k), .ldr .r2 .r0 (ACC + 64 + 4 * k), .mul .r2 .r2 .r8,
    .dp .add .r3 .r3 (.reg .r2)]

/-- `[o] = [a] · [b]` (`o` may be `a` or `b`). -/
def mul (o a b : Nat) : Prog isa :=
  .seq (.block (prologue ++ zeroAcc ++ [.mov .r7 (.reg .r0), .mov .r9 (.imm 16)]))
    (.seq (.loop (.block (row a b)) .ne) (.block (.mov .r5 (.imm 0) :: pass .r0 o mulSrc ++ tail o)))

end VG.Impl.Ed25519.Arm
