import VerifiedGarbage.Impl.Ed25519.Arm.Packed

/-! Expand a sixteen-bit scalar digit into the batch buffer. Only immediate
shifts are needed; the table and loop addresses depend on public indices. -/
namespace VG.Impl.Ed25519.Arm
open VG.Arm

def expandBit (k : Nat) : List Instr :=
  [.dp .and .r9 .r3 (.imm 1), .strb .r9 .r0 (32 + k), .mov .r3 (.shifted .r3 .lsr 1)]

def expandBits : List Instr := (List.range 16).flatMap expandBit

def batchDigit : List Instr :=
  [.ldr .r12 .r0 52, .ldr .r2 .r0 56, .dp .add .r12 .r12 (.shifted .r2 .lsl 1)] ++
  unpackSrc 0 0

def batchBits : List Instr := batchDigit ++ expandBits

end VG.Impl.Ed25519.Arm
