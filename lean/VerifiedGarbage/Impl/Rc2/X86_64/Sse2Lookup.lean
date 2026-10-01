import VerifiedGarbage.Impl.Rc2.X86_64.Lookup

/-! # Eight-way constant-time RC2 scans on baseline x86-64

SSE2 is part of the target baseline. Each word-sized XOR is at most 255;
subtracting one and shifting arithmetically produces a full equality mask.
The scans visit every candidate in order, eight candidates per vector.
The temporary vector store is restored before returning.
-/

namespace VG.Impl.Rc2.X86_64.Sse2

open VG.X86_64 VG.Impl.Rc2.X86_64

def loadConst (dst : XReg) (v : BitVec 128) : List Instr :=
  [.movImm64 .r10 (v.extractLsb' 0 64), .xop (.movq dst .r10),
   .movImm64 .r10 (v.extractLsb' 64 64), .xop (.movq .xmm5 .r10),
   .xop (.bin .punpcklqdq dst .xmm5)]

def indices (n : Nat) : BitVec 128 := ofWords fun j => BitVec.ofNat 16 (8 * n + j)
def ones : BitVec 128 := ofWords fun _ => 1
def eights : BitVec 128 := ofWords fun _ => 8
def piValues (n : Nat) : BitVec 128 :=
  ofWords fun j => (VG.Spec.Rc2.piTable.getD (8 * n + j) 0).setWidth 16

def start (scratch : Reg) (mask : Nat) : List Instr :=
  [.movdquLoad .xmm8 (memOp scratch 64), .alu .and .rax (.imm (BitVec.ofNat 32 mask)),
   .xop (.movq .xmm0 .rax), .xop (.bin .punpcklwd .xmm0 .xmm0),
   .xop (.pshufd .xmm0 .xmm0 0), .xop (.bin .pxor .xmm1 .xmm1)] ++
   loadConst .xmm2 (indices 0) ++ loadConst .xmm6 ones ++ loadConst .xmm7 eights

def select : List Instr :=
  [.xop (.bin .movdqa .xmm3 .xmm0), .xop (.bin .pxor .xmm3 .xmm2),
   .xop (.bin .psubw .xmm3 .xmm6), .xop (.shift .psraw .xmm3 15),
   .xop (.bin .pand .xmm3 .xmm4), .xop (.bin .por .xmm1 .xmm3),
   .xop (.bin .paddw .xmm2 .xmm7)]

def piStep (n : Nat) : List Instr := loadConst .xmm4 (piValues n) ++ select

def reduceOr : List Instr :=
  [8, 4, 2].flatMap fun n =>
    [.xop (.bin .movdqa .xmm3 .xmm1), .xop (.shift .psrldq .xmm3 (BitVec.ofNat 8 n)),
     .xop (.bin .por .xmm1 .xmm3)]

def finish (scratch : Reg) : List Instr := reduceOr ++
  [.movdquStore (memOp scratch 64) .xmm1, .mov .rax (.mem (memOp scratch 64)),
   .alu .and .rax (.imm 65535), .movdquStore (memOp scratch 64) .xmm8]

def piLookup : List Instr :=
  start .r8 255 ++ (List.range 32).flatMap piStep ++ finish .r8

end VG.Impl.Rc2.X86_64.Sse2
