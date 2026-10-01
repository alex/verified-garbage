import VerifiedGarbage.Impl.X25519.X86

/-! Expand an unsigned scalar at esi into one byte per bit, at edi+7168.
Only fixed addresses are used; bytes is32 for scalarbase and64 forchallenge. -/
namespace VG.Impl.Ed25519.X86
open VG.X86 VG.Impl.X25519.X86

def expandScalarBit (k : Nat) : List Instr :=
  [.movzx8 .eax (at_ .esi (k / 8)), .alu .add .eax (.reg .eax),
    .shift .shr .eax (k % 8 + 1), .alu .and .eax (.imm 1), .store8 (sc (7168 + k)) .al]

def expandScalarBits (bytes : Nat) : List Instr := (List.range (8 * bytes)).flatMap expandScalarBit

def loadScalarBits (bytes : Nat) : List Instr :=
  .mov .esi (.mem (sc 20)) :: expandScalarBits bytes
end VG.Impl.Ed25519.X86
