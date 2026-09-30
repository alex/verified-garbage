import VerifiedGarbage.Impl.Ed25519.Arm.Word
import VerifiedGarbage.Spec.Ed25519

/-! Scalar arithmetic modulo the Ed25519 subgroup order. All carries use
16-bit limbs and baseline 32-bit instructions. -/
namespace VG.Impl.Ed25519.Arm
open VG VG.Arm

/-- The running remainder and the candidate after subtracting L. -/
def SR : Nat := 256
def SD : Nat := 320

/-- The radix-65536 complement of L, without its final carry-in. -/
def scalarComplement (k : Nat) : Nat := 65535 - Spec.Ed25519.L / 2 ^ (16 * k) % 65536

def scalarDoubleSrc (k : Nat) : List Instr :=
  [.ldr .r3 .r0 (SR + 4 * k), .dp .add .r3 .r3 (.reg .r3)]

def scalarSubtractSrc (k : Nat) : List Instr :=
  [.ldr .r3 .r0 (SR + 4 * k), .movw .r2 (BitVec.ofNat 16 (scalarComplement k)),
    .dp .add .r3 .r3 (.reg .r2)]

def scalarBitSource (j : Nat) : Op2 :=
  if j = 0 then .reg .r11 else .shifted .r11 .lsr j

/-- Consume bit j of r11, doubling the remainder and subtracting L if
necessary. r10 and r12 are preserved for the byte counter and input pointer. -/
def scalarBit (j : Nat) : List Instr :=
  [.mov .r5 (scalarBitSource j), .dp .and .r5 .r5 (.imm 1), .movw .r6 65535] ++
    pass .r0 SR scalarDoubleSrc ++ [.mov .r5 (.imm 1)] ++
    pass .r0 SD scalarSubtractSrc ++
    [.mov .r9 (.imm 0), .dp .sub .r9 .r9 (.reg .r5)] ++ cswap SR SD

def scalarRead : List Instr :=
  [.dp .sub .r10 .r10 (.imm 1), .dp .add .r2 .r12 (.reg .r10), .ldrb .r11 .r2 0]

def scalarByte : List Instr :=
  scalarRead ++ (List.range 8).reverse.flatMap scalarBit ++ [.cmp .r10 (.imm 0)]

def scalarInit : List Instr :=
  [.mov .r3 (.imm 0)] ++ storeN .r3 SR 16 ++ [.mov .r10 (.imm 64)]

/-- Read the complete 64-byte integer from r12. -/
def scalarReduceEngine : Prog isa :=
  .seq (.block scalarInit) (.loop (.block scalarByte) .ne)

/-- Exact 256-by-256 multiplication, before any modular reduction. -/
def scalarWideMul (x y : Nat) : Prog isa :=
  .seq (.block (prologue ++ zeroAcc ++ [.mov .r7 (.reg .r0), .mov .r9 (.imm 16)]))
    (.loop (.block (row x y)) .ne)

end VG.Impl.Ed25519.Arm
