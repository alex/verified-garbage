import VerifiedGarbage.Spec.Gcm
import VerifiedGarbage.TCB.X86.Isa

/-!
8-XMM PCLMUL GHASH, verified against the shared GHASH contract using the
reviewed x86 SIMD model. The reflected field arithmetic matches the
reviewed x86-64 implementation, using one block at a time to fit eight XMMs.
All GPR writes are caller-saved (eax, ecx, edx), so stack use is zero.
-/
namespace VG.Impl.Gcm.X86.Pclmul
open VG.X86

def at_ (b : Reg) (d : Nat) : MemOp := { base := b, disp := d }
def argOp (i : Nat) : MemOp := at_ .esp (4 + 4 * i)
def revMask : BitVec 128 := 0x000102030405060708090a0b0c0d0e0f#128
def poly : BitVec 128 := 0xc2000000000000000000000000000000#128
def xInv : BitVec 128 := 0xc2000000000000000000000000000001#128

/-- Build a constant in registers; xmm5 is free during setup. -/
def const (x : XReg) (c : BitVec 128) : List Instr :=
  [.mov .eax (.imm (c.extractLsb' 96 32)), .xop (.movd x .eax)] ++
  (List.range 3).flatMap (fun k =>
    [.xop (.shift .pslldq x 4), .mov .eax (.imm (c.extractLsb' (32 * (2 - k)) 32)),
     .xop (.movd .xmm5 .eax), .xop (.bin .por x .xmm5)])

/-! xmm0 reversal, xmm1 polynomial, xmm2 Y/input, xmm3 H*x^-1,
xmm4 lo, xmm5 mid, xmm6 hi, xmm7 temporary. -/

def zero : List Instr :=
  [.xop (.bin .pxor .xmm4 .xmm4), .xop (.bin .pxor .xmm5 .xmm5),
   .xop (.bin .pxor .xmm6 .xmm6)]

def acc : List Instr :=
  [.xop (.bin .movdqa .xmm7 .xmm2), .xop (.pclmulqdq .xmm7 .xmm3 0x00),
   .xop (.bin .pxor .xmm4 .xmm7),
   .xop (.bin .movdqa .xmm7 .xmm2), .xop (.pclmulqdq .xmm7 .xmm3 0x11),
   .xop (.bin .pxor .xmm6 .xmm7),
   .xop (.bin .movdqa .xmm7 .xmm2), .xop (.pclmulqdq .xmm7 .xmm3 0x01),
   .xop (.bin .pxor .xmm5 .xmm7),
   .xop (.bin .movdqa .xmm7 .xmm2), .xop (.pclmulqdq .xmm7 .xmm3 0x10),
   .xop (.bin .pxor .xmm5 .xmm7)]

def fold : List Instr :=
  [.xop (.bin .movdqa .xmm7 .xmm4), .xop (.pclmulqdq .xmm7 .xmm1 0x10),
   .xop (.pshufd .xmm4 .xmm4 0x4e), .xop (.bin .pxor .xmm4 .xmm7)]

def reduce : List Instr :=
  [.xop (.bin .movdqa .xmm7 .xmm5), .xop (.shift .psrldq .xmm7 8),
   .xop (.bin .pxor .xmm6 .xmm7), .xop (.shift .pslldq .xmm5 8),
   .xop (.bin .pxor .xmm4 .xmm5)] ++ fold ++ fold ++
  [.xop (.bin .movdqa .xmm2 .xmm6), .xop (.bin .pxor .xmm2 .xmm4)]

/-- H arrives in xmm7; xmm4/xmm5/xmm6 are available during setup. -/
def hInv : List Instr :=
  const .xmm4 xInv ++
  [.mov .eax (.imm 0xffffffff), .xop (.movd .xmm5 .eax),
   .xop (.bin .punpckldq .xmm5 .xmm5), .xop (.bin .punpcklqdq .xmm5 .xmm5),
   .xop (.bin .movdqa .xmm3 .xmm7), .xop (.shift .psllq .xmm3 1),
   .xop (.bin .movdqa .xmm6 .xmm7), .xop (.shift .psrlq .xmm6 63),
   .xop (.shift .pslldq .xmm6 8), .xop (.bin .por .xmm3 .xmm6),
   .xop (.pshufd .xmm6 .xmm7 0xff), .xop (.shift .psrld .xmm6 31),
   .xop (.bin .paddd .xmm6 .xmm5), .xop (.bin .pandn .xmm6 .xmm4),
   .xop (.bin .pxor .xmm3 .xmm6)]

def prologue : List Instr :=
  const .xmm0 revMask ++ const .xmm1 poly ++
  [.mov .eax (.mem (argOp 0)), .movdquLoad .xmm7 (at_ .eax 0),
   .xop (.bin .pshufb .xmm7 .xmm0)] ++ hInv ++
  [.mov .ecx (.mem (argOp 1)), .movdquLoad .xmm2 (at_ .ecx 0),
   .xop (.bin .pshufb .xmm2 .xmm0), .mov .edx (.mem (argOp 2)),
   .mov .eax (.mem (argOp 3)), .alu .test .eax (.reg .eax)]

def body : List Instr :=
  [.movdquLoad .xmm7 (at_ .edx 0), .xop (.bin .pshufb .xmm7 .xmm0),
   .xop (.bin .pxor .xmm2 .xmm7)] ++ zero ++ acc ++ reduce ++
  [.alu .add .edx (.imm 16), .alu .sub .eax (.imm 1)]

def epilogue : List Instr :=
  [.xop (.bin .pshufb .xmm2 .xmm0), .movdquStore (at_ .ecx 0) .xmm2]

def ghash : Prog isa :=
  .seq (.block prologue)
    (.seq (.ite .e (.block []) (.loop (.block body) .ne)) (.block epilogue))

end VG.Impl.Gcm.X86.Pclmul
