import VerifiedGarbage.Impl.Sha256.X86

/-!
# SHA-256 compression on x86 with SHA extensions

Eight XMM registers hold ABEF, CDGH, four message quads, the round operand,
and one temporary. The endian mask and saved hash vectors live in the existing
112-byte scratch region; the cdecl stack and callee-saved GPRs are preserved.
SHA-NI and SSSE3 are required.
-/
namespace VG.Impl.Sha256.X86.ShaNi
open VG.X86
open VG.Spec.Sha256 (K)

def at_ (b : Reg) (d : Nat) : MemOp := { base := b, disp := d }
def msg (i : Nat) : XReg := [.xmm3, .xmm4, .xmm5, .xmm6].getD (i % 4) .xmm3

def kQuad (i : Nat) : BitVec 128 := ofDwords (K i) (K (i + 1)) (K (i + 2)) (K (i + 3))
def bswapMask : BitVec 128 := 0x0c0d0e0f08090a0b0405060700010203#128

/-- Assemble a constant in XMM0 using XMM7, with no memory round trip. -/
def const (c : BitVec 128) : List Instr :=
  [.mov .eax (.imm (dword c 0)), .xop (.movd .xmm0 .eax),
   .mov .eax (.imm (dword c 1)), .xop (.movd .xmm7 .eax),
   .xop (.bin .punpckldq .xmm0 .xmm7),
   .mov .eax (.imm (dword c 2)), .xop (.movd .xmm7 .eax),
   .xop (.bin .punpcklqdq .xmm0 .xmm7),
   .mov .eax (.imm (dword c 3)), .xop (.movd .xmm7 .eax),
   .xop (.shift .pslldq .xmm7 12), .xop (.bin .por .xmm0 .xmm7)]

/-- Initial message quads use the endian mask stored at scratch + 16. -/
def schedule (i : Nat) : List Instr :=
  if i < 4 then
    [.movdquLoad (msg i) (at_ .edi (16 * i)), .movdquLoad .xmm0 (at_ .esi 16),
     .xop (.bin .pshufb (msg i) .xmm0)]
  else
    [.xop (.bin .sha256msg1 (msg i) (msg (i + 1))),
     .xop (.bin .movdqa .xmm7 (msg (i + 3))),
     .xop (.palignr .xmm7 (msg (i + 2)) 4),
     .xop (.bin .paddd (msg i) .xmm7),
     .xop (.bin .sha256msg2 (msg i) (msg (i + 3)))]

def roundOps (i : Nat) : List Instr :=
  [.xop (.bin .paddd .xmm0 (msg i)),
   .xop (.sha256rnds2 .xmm2 .xmm1),
   .xop (.pshufd .xmm0 .xmm0 0x0e),
   .xop (.sha256rnds2 .xmm1 .xmm2)]

def rounds4 (i : Nat) : List Instr := const (kQuad (4 * i)) ++ roundOps i

def rounds : Nat → Prog isa
  | 0 => .block []
  | n + 1 => .seq (rounds n) (.block (schedule n ++ rounds4 n))

def saveHash : List Instr :=
  [.movdquStore (at_ .esi 32) .xmm1, .movdquStore (at_ .esi 48) .xmm2]

def finishBlock : List Instr :=
  [.movdquLoad .xmm7 (at_ .esi 32), .xop (.bin .paddd .xmm1 .xmm7),
   .movdquLoad .xmm7 (at_ .esi 48), .xop (.bin .paddd .xmm2 .xmm7),
   .alu .add .edi (.imm 64), .alu .sub .ebp (.imm 1)]

def body : Prog isa :=
  .seq (.block saveHash) (.seq (rounds 16) (.block finishBlock))

def prologue : List Instr := VG.Impl.Sha256.X86.prologue
def epilogue : List Instr := VG.Impl.Sha256.X86.epilogue

def loadState : List Instr :=
  [.movdquLoad .xmm1 (at_ .ebx 0), .movdquLoad .xmm2 (at_ .ebx 16),
   .xop (.pshufd .xmm1 .xmm1 0xb1), .xop (.pshufd .xmm2 .xmm2 0xb1),
   .xop (.bin .movdqa .xmm7 .xmm2), .xop (.bin .punpcklqdq .xmm7 .xmm1),
   .xop (.bin .punpckhqdq .xmm2 .xmm1), .xop (.bin .movdqa .xmm1 .xmm7)]

def load : List Instr :=
  ([.mov .ebx (.mem (at_ .esp 4))] : List Instr) ++ const bswapMask ++
  ([.movdquStore (at_ .esi 16) .xmm0] : List Instr) ++ loadState

def store : List Instr :=
  [.xop (.bin .movdqa .xmm7 .xmm1), .xop (.bin .punpckhqdq .xmm7 .xmm2),
   .xop (.bin .punpcklqdq .xmm1 .xmm2), .xop (.pshufd .xmm7 .xmm7 0xb1),
   .xop (.pshufd .xmm1 .xmm1 0xb1),
   .movdquStore (at_ .ebx 0) .xmm7, .movdquStore (at_ .ebx 16) .xmm1]

def compress : Prog isa :=
  .seq (.block prologue)
    (.seq (.block load)
      (.seq (.ite .e (.block []) (.loop body .ne)) (.block (store ++ epilogue))))
end VG.Impl.Sha256.X86.ShaNi
