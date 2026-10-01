import VerifiedGarbage.TCB.Arm.Isa

/-! Argument setup for whole Ed25519 operations. Saved caller arguments live
in the read-only stack allocation, beyond the writable local frame. -/
namespace VG.Impl.Ed25519.Arm.Whole
open VG.Arm

inductive Value where
  | const (n : Nat)
  | frame (offset : Nat)
  | caller (index offset : Nat)

def setArg (r : Reg) : Value → List Instr
  | .const n => [.movw r (BitVec.ofNat 16 n)]
  | .frame d => [.addSp r d]
  | .caller j d => [.ldrSp r (248 + 4 * j), .dp .add r r (.imm (BitVec.ofNat 32 d))]

def putArg (j : Nat) (v : Value) : List Instr :=
  setArg .r0 v ++ [.addSp .r12 (4 * j), .str .r0 .r12 0]

def setupStack (start : Nat) : List Value → List Instr
  | [] => []
  | v :: vs => putArg start v ++ setupStack (start + 1) vs

def setup (args : List (Reg × Value)) (stack : List Value) : List Instr :=
  setupStack 0 stack ++
    args.flatMap fun (r,v) => setArg r v

def callWith (args : List Instr) (name : String) (code : Prog isa) : Prog isa :=
  .seq (.block args) (.call name code)

end VG.Impl.Ed25519.Arm.Whole
