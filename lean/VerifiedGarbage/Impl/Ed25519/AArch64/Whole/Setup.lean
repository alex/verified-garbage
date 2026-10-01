import VerifiedGarbage.TCB.AArch64.Isa

/-! Register argument setup for whole Ed25519 operations. Original arguments
are saved in the read-only part of the local stack allocation. -/
namespace VG.Impl.Ed25519.AArch64.Whole
open VG.AArch64

inductive Value where
  | const (n : Nat)
  | frame (offset : Nat)
  | caller (index offset : Nat)

def setArg (r : Reg) : Value → List Instr
  | .const n => [.movz .x r (BitVec.ofNat 16 n) 0]
  | .frame d => [.addSp r d]
  | .caller j d => [.ldrSp r (256 + 8 * j), .addImm .x r r d]

def setup (args : List (Reg × Value)) : List Instr :=
  args.flatMap fun (r, v) => setArg r v

def callWith (args : List Instr) (name : String) (code : Prog isa) : Prog isa :=
  .seq (.block args) (.call name code)

end VG.Impl.Ed25519.AArch64.Whole
