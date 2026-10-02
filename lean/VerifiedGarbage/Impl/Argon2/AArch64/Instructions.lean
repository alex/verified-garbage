import VerifiedGarbage.Impl.Blake2.AArch64

/-! # Scalar operations for the ARM64 Argon2 driver

x12 and x13 are operand temporaries. x15 retains the most recent arithmetic
result for CBZ/CBNZ. Comparisons use SUBS and x14 retains its borrow mask;
SBCS can consume carry directly. The compared counters fit in 32 bits,
so the high bit of their 64-bit difference is the unsigned-borrow marker. These are all caller-saved registers.
-/
namespace VG.Impl.Argon2.AArch64.Instructions
open VG.AArch64

def mov (d n : Reg) : List Instr := [.addImm .x d n 0]
def mov32 (d n : Reg) : List Instr := [.logic .orr .w d n n]
def imm (d : Reg) (n : Nat) : List Instr :=
  if n < 65536 then [.movz .x d (BitVec.ofNat 16 n) 0]
  else VG.Impl.Blake2.AArch64.movImm64 d (BitVec.ofNat 64 n)
def load (d n : Reg) (off : Nat := 0) : List Instr := [.ldr .x d n off]
def store (n : Reg) (off : Nat) (d : Reg) : List Instr := [.str .x d n off]
def store32 (n : Reg) (off : Nat) (d : Reg) : List Instr := [.str .w d n off]
def mark (d : Reg) : List Instr := mov .x15 d

def add (d n : Reg) : List Instr := [.add .x d d n] ++ mark d
def addi (d : Reg) (n : Nat) : List Instr :=
  (if n < 4096 then [.addImm .x d d n] else imm .x12 n ++ [.add .x d d .x12]) ++ mark d
def sub (d n : Reg) : List Instr := [.subs .x d d n] ++ mark d
def subi (d : Reg) (n : Nat) : List Instr := imm .x12 n ++ sub d .x12

def logic (op : LogicOp) (d n : Reg) : List Instr := [.logic op .x d d n] ++ mark d
def logici (op : LogicOp) (d : Reg) (n : Nat) : List Instr := imm .x12 n ++ logic op d .x12

def compare (d n : Reg) : List Instr :=
  [.subs .x .x15 d n, .lsr .x .x14 .x15 63]
def comparei (d : Reg) (n : Nat) : List Instr := imm .x13 n ++ compare d .x13
def comparem (d n : Reg) (off : Nat := 0) : List Instr := load .x13 n off ++ compare d .x13

def sbb (d : Reg) : List Instr := [.sbcs .x d d d] ++ mark d
def mul (n : Reg) : List Instr := [.umulh .x2 .x8 n, .mul .x .x8 .x8 n]
def shr (d : Reg) (n : Nat) : List Instr := [.lsr .x d d n] ++ mark d

def xorm (d n : Reg) (off : Nat) : List Instr := load .x13 n off ++ logic .eor d .x13
end VG.Impl.Argon2.AArch64.Instructions
