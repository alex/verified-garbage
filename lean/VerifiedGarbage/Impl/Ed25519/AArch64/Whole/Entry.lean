import VerifiedGarbage.TCB.AArch64.Isa

/-! Shared saved arguments and stack frame for complete Ed25519 operations. -/
namespace VG.Impl.Ed25519.AArch64.Whole
open VG.AArch64

def argReg (j : Nat) : Reg :=
  match j with | 0 => .x0 | 1 => .x1 | 2 => .x2 | 3 => .x3 | 4 => .x4 | _ => .x5

def saveWord (j : Nat) : List Instr :=
  [.addSp .x15 (256 + 8 * j), .str .x (argReg j) .x15 0]

def saveArgs : List Instr := (List.range 6).flatMap saveWord

def wrap (body : Prog isa) : Prog isa :=
  .frame (.push .x30)
    (.frame (.alloc 320) (.seq (.block saveArgs) body) (.free 320)) (.pop .x30)

end VG.Impl.Ed25519.AArch64.Whole
