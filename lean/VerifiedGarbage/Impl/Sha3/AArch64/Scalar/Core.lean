import VerifiedGarbage.TCB.AArch64.Isa
import VerifiedGarbage.Spec.Sha3

/-!
Portable scalar Keccak schedule following OpenSSL's scalar KeccakF1600_int:
https://github.com/openssl/openssl/blob/openssl-3.6.0/crypto/sha/asm/keccak1600-armv8.pl
Twenty-five state lanes remain in general registers. x18 and x29 are excluded.
Two temporary lane spills supply the extra parity registers required by theta.
The abstract operations are mapped to reviewed ISA instructions separately.
-/
namespace VG.Impl.Sha3.AArch64.Scalar
open VG VG.AArch64
abbrev Lane := Spec.Sha3.Lane

def laneReg (i : Nat) : Reg :=
  match i with
  | 0 => .x0
  | 1 => .x1
  | 2 => .x2
  | 3 => .x3
  | 4 => .x4
  | 5 => .x5
  | 6 => .x6
  | 7 => .x7
  | 8 => .x8
  | 9 => .x9
  | 10 => .x10
  | 11 => .x11
  | 12 => .x12
  | 13 => .x13
  | 14 => .x14
  | 15 => .x15
  | 16 => .x16
  | 17 => .x17
  | 18 => .x25
  | 19 => .x19
  | 20 => .x20
  | 21 => .x21
  | 22 => .x22
  | 23 => .x23
  | 24 => .x24
  | _ => .x0

def thetaReg (i : Nat) : Reg :=
  if i = 2 then .x27 else if i = 3 then .x26 else if i = 4 then .x28 else laneReg i

inductive ScalarOp where
  | xor (dst a b : Reg)
  | xorRor (dst a b : Reg) (n : Nat)
  | bic (dst a b : Reg)
  | bicRor (dst a b : Reg) (n : Nat)
  | ror (dst a : Reg) (n : Nat)
  | move (dst a : Reg)
  | spill (slot : Nat) (a : Reg)
  | reload (dst : Reg) (slot : Nat)
  deriving Repr

structure File where
  regs : Reg → Lane
  slots : Nat → Lane

def File.write (f : File) (r : Reg) (v : Lane) : File :=
  { f with regs := fun q => if q = r then v else f.regs q }

def step (f : File) : ScalarOp → File
  | .xor d a b => f.write d (f.regs a ^^^ f.regs b)
  | .xorRor d a b n => f.write d (f.regs a ^^^ (f.regs b).rotateRight n)
  | .bic d a b => f.write d (f.regs a &&& ~~~f.regs b)
  | .bicRor d a b n => f.write d (f.regs a &&& ~~~(f.regs b).rotateRight n)
  | .ror d a n => f.write d ((f.regs a).rotateRight n)
  | .move d a => f.write d (f.regs a)
  | .spill k a => { f with slots := fun j => if j = k then f.regs a else f.slots j }
  | .reload d k => f.write d (f.slots k)

def run (ops : List ScalarOp) (f : File) : File := ops.foldl step f

def thetaOps : List ScalarOp :=
  [.xor .x26 .x0 .x5,
   .spill 0 .x4,
   .spill 1 .x9,
   .xor .x27 .x1 .x6,
   .xor .x28 .x2 .x7,
   .xor .x30 .x3 .x8,
   .xor .x4 .x4 .x9,
   .xor .x26 .x26 .x10,
   .xor .x27 .x27 .x11,
   .xor .x28 .x28 .x12,
   .xor .x30 .x30 .x13,
   .xor .x4 .x4 .x14,
   .xor .x26 .x26 .x15,
   .xor .x27 .x27 .x16,
   .xor .x28 .x28 .x17,
   .xor .x30 .x30 .x25,
   .xor .x4 .x4 .x19,
   .xor .x26 .x26 .x20,
   .xor .x27 .x27 .x21,
   .xor .x28 .x28 .x22,
   .xor .x30 .x30 .x23,
   .xor .x4 .x4 .x24,
   .xorRor .x9 .x26 .x28 63,
   .xor .x1 .x1 .x9,
   .xor .x6 .x6 .x9,
   .xor .x11 .x11 .x9,
   .xor .x16 .x16 .x9,
   .xor .x21 .x21 .x9,
   .xorRor .x9 .x27 .x30 63,
   .xorRor .x28 .x28 .x4 63,
   .xorRor .x30 .x30 .x26 63,
   .xorRor .x4 .x4 .x27 63,
   .xor .x27 .x2 .x9,
   .xor .x7 .x7 .x9,
   .xor .x12 .x12 .x9,
   .xor .x17 .x17 .x9,
   .xor .x22 .x22 .x9,
   .xor .x0 .x0 .x4,
   .xor .x5 .x5 .x4,
   .xor .x10 .x10 .x4,
   .xor .x15 .x15 .x4,
   .xor .x20 .x20 .x4,
   .reload .x4 0,
   .reload .x9 1,
   .xor .x26 .x3 .x28,
   .xor .x8 .x8 .x28,
   .xor .x13 .x13 .x28,
   .xor .x25 .x25 .x28,
   .xor .x23 .x23 .x28,
   .xor .x28 .x4 .x30,
   .xor .x9 .x9 .x30,
   .xor .x14 .x14 .x30,
   .xor .x19 .x19 .x30,
   .xor .x24 .x24 .x30]

def rhoPiOps : List ScalarOp :=
  [.move .x30 .x1,
   .ror .x1 .x6 20,
   .ror .x2 .x12 21,
   .ror .x3 .x25 43,
   .ror .x4 .x24 50,
   .ror .x6 .x9 44,
   .ror .x12 .x13 39,
   .ror .x25 .x17 49,
   .ror .x24 .x21 62,
   .ror .x9 .x22 3,
   .ror .x13 .x19 56,
   .ror .x17 .x11 54,
   .ror .x21 .x8 9,
   .ror .x22 .x14 25,
   .ror .x19 .x23 8,
   .ror .x11 .x7 58,
   .ror .x8 .x16 19,
   .ror .x14 .x20 46,
   .ror .x23 .x15 23,
   .ror .x7 .x10 61,
   .ror .x16 .x5 28,
   .ror .x5 .x26 36,
   .ror .x10 .x30 63,
   .ror .x15 .x28 37,
   .ror .x20 .x27 2]

def chiOps : List ScalarOp :=
  [.bic .x26 .x2 .x1,
   .bic .x27 .x3 .x2,
   .bic .x28 .x0 .x4,
   .bic .x30 .x1 .x0,
   .xor .x0 .x0 .x26,
   .bic .x26 .x4 .x3,
   .xor .x1 .x1 .x27,
   .xor .x3 .x3 .x28,
   .xor .x4 .x4 .x30,
   .xor .x2 .x2 .x26,
   .bic .x26 .x7 .x6,
   .bic .x27 .x8 .x7,
   .bic .x28 .x5 .x9,
   .bic .x30 .x6 .x5,
   .xor .x5 .x5 .x26,
   .bic .x26 .x9 .x8,
   .xor .x6 .x6 .x27,
   .xor .x8 .x8 .x28,
   .xor .x9 .x9 .x30,
   .xor .x7 .x7 .x26,
   .bic .x26 .x12 .x11,
   .bic .x27 .x13 .x12,
   .bic .x28 .x10 .x14,
   .bic .x30 .x11 .x10,
   .xor .x10 .x10 .x26,
   .bic .x26 .x14 .x13,
   .xor .x11 .x11 .x27,
   .xor .x13 .x13 .x28,
   .xor .x14 .x14 .x30,
   .xor .x12 .x12 .x26,
   .bic .x26 .x17 .x16,
   .bic .x27 .x25 .x17,
   .bic .x28 .x15 .x19,
   .bic .x30 .x16 .x15,
   .xor .x15 .x15 .x26,
   .bic .x26 .x19 .x25,
   .xor .x16 .x16 .x27,
   .xor .x25 .x25 .x28,
   .xor .x19 .x19 .x30,
   .xor .x17 .x17 .x26,
   .bic .x26 .x22 .x21,
   .bic .x27 .x23 .x22,
   .bic .x28 .x20 .x24,
   .bic .x30 .x21 .x20,
   .xor .x20 .x20 .x26,
   .bic .x26 .x24 .x23,
   .xor .x21 .x21 .x27,
   .xor .x23 .x23 .x28,
   .xor .x24 .x24 .x30,
   .xor .x22 .x22 .x26]

end VG.Impl.Sha3.AArch64.Scalar
