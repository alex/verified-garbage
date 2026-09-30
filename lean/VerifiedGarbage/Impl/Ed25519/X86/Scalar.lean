import VerifiedGarbage.Impl.Ed25519.X86.CommonMemory
import VerifiedGarbage.Spec.Ed25519

/-! Binary scalar reduction uses eight 32-bit limbs in scratch. Every bit
performs a doubling and one masked subtraction of the subgroup order. -/
namespace VG.Impl.Ed25519.X86
open VG.X86 VG.Impl.X25519.X86

def scalarR : Nat := 64

def scalarK (k : Nat) : BitVec 32 :=
  BitVec.ofNat 32 ((2 ^ 256 - VG.Spec.Ed25519.L) / 2 ^ (32 * k))

def scalarDouble : List Instr :=
  cols scalarR 8 (fun k => [.mulI (scalarR + 4 * k) 2])

def scalarSubtract : List Instr := zeroAcc ++
  cols T 8 (fun k => [.addM (scalarR + 4 * k), .addI (scalarK k)])

def scalarMask : List Instr := [.mov .ecx (.imm 0), .alu .sub .ecx (.reg .ebx)]

def scalarSelect : List Instr := (List.range 8).flatMap fun k =>
  [.mov .eax (.mem (sc (scalarR + 4 * k))), .mov .edx (.mem (sc (T + 4 * k))),
    .alu .xor .edx (.reg .eax), .alu .and .edx (.reg .ecx),
    .alu .xor .eax (.reg .edx), .store (sc (scalarR + 4 * k)) .eax]

def scalarRound : List Instr := scalarDouble ++ scalarSubtract ++ scalarMask ++ scalarSelect
/-- The byte is doubled at offset32, so all shifts have nonzero immediates. -/
def scalarBitLoad (j : Nat) : List Instr :=
  [.mov .ebx (.mem (sc 32)), .shift .shr .ebx (j + 1), .alu .and .ebx (.imm 1),
    .mov .ecx (.imm 0), .mov .ebp (.imm 0)]

def scalarBit (j : Nat) : List Instr := scalarBitLoad j ++ scalarRound

def scalarBits (n : Nat) : List Instr := (List.range n).reverse.flatMap scalarBit

def scalarRead : List Instr :=
  [.alu .sub .esi (.imm 1), .mov .eax (.reg .edi), .alu .add .eax (.reg .esi),
    .movzx8 .eax (at_ .eax 128), .alu .add .eax (.reg .eax), .store (sc 32) .eax]

def scalarByte : List Instr := scalarRead ++ scalarBits 8 ++ [.alu .test .esi (.reg .esi)]

def scalarInit : List Instr := zeroAcc ++ cols scalarR 8 (fun _ => []) ++ [.mov .esi (.imm 64)]

def scalarEngine : Prog isa := .seq (.block scalarInit) (.loop (.block scalarByte) .ne)

def scalarReduce : Prog isa :=
  .seq (.block (abiSave 2 ++ ([.mov .esi (.mem (at_ .esp 8))] : List Instr) ++ copyWords 128 16))
    (.seq scalarEngine (.block (finishWords scalarR)))
end VG.Impl.Ed25519.X86
