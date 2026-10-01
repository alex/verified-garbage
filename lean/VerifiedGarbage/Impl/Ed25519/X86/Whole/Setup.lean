import VerifiedGarbage.TCB.X86.Isa

/-! Small argument-setup blocks shared by the complete Ed25519 operations. -/
namespace VG.Impl.Ed25519.X86.Whole
open VG.X86

def at_ (d : Nat) : MemOp := { base := .esp, disp := d }

inductive Value where
  | const (n : Nat)
  | frame (offset : Nat)
  | caller (index offset : Nat)

def load : Value → List Instr
  | .const n => [.mov .eax (.imm (BitVec.ofNat 32 n))]
  | .frame d => [.mov .eax (.reg .esp), .alu .add .eax (.imm (BitVec.ofNat 32 d))]
  | .caller i d => [.mov .eax (.mem (at_ (260 + 4 * i))),
      .alu .add .eax (.imm (BitVec.ofNat 32 d))]

def put (slot : Nat) (v : Value) : List Instr := load v ++ [.store (at_ (4 * slot)) .eax]

def setup (start : Nat) : List Value → List Instr
  | [] => []
  | v :: vs => put start v ++ setup (start + 1) vs

/-- Add a fixed prefix length to a caller's 32-bit length, preserving the
carry in the high half of SHA-512's 64-bit outgoing count. -/
def countArgs (index prefixLen : Nat) : List Instr :=
  [.mov .eax (.mem (at_ (260 + 4 * index))), .mov .edx (.imm 0),
   .alu .add .eax (.imm (BitVec.ofNat 32 prefixLen)), .alu .adc .edx (.imm 0),
   .store (at_ 4) .eax, .store (at_ 8) .edx]

end VG.Impl.Ed25519.X86.Whole
