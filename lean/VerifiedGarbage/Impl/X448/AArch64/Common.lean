import VerifiedGarbage.TCB.AArch64.Isa

/-! Shared register access and field-slot layout for AArch64 X448. -/
namespace VG.Impl.X448.AArch64

open VG.AArch64

/-- A word in the working space. -/
def ld (r : Reg) (d : Nat) : Instr := .ldr .x r .x3 d
def st (r : Reg) (d : Nat) : Instr := .str .x r .x3 d

/-- Each field element occupies 128 bytes. -/
def slot (n : Nat) : Nat := 64 + 128 * n
def X1 : Nat := slot 0
def X2 : Nat := slot 1
def Z2 : Nat := slot 2
def X3 : Nat := slot 3
def Z3 : Nat := slot 4
def A : Nat := slot 5
def B : Nat := slot 6
def C : Nat := slot 7
def D : Nat := slot 8
def AA : Nat := slot 9
def BB : Nat := slot 10
def E : Nat := slot 11
def DA : Nat := slot 12
def CB : Nat := slot 13
def T0 : Nat := slot 14
def T1 : Nat := slot 15
def T2 : Nat := slot 16
def T3 : Nat := slot 17
def T4 : Nat := slot 18
def T5 : Nat := slot 19
def T6 : Nat := slot 20
def T7 : Nat := slot 21
def SWAP : Nat := 16
def BITS : Nat := 3072
def ACC : Nat := 3584
def TMP : Nat := 3840

end VG.Impl.X448.AArch64
