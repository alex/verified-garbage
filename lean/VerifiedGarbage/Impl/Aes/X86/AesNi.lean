import VerifiedGarbage.Spec.Aes
import VerifiedGarbage.TCB.X86.Isa

/-!
Draft 32-bit AES-NI implementation. Not registered or proven; only usable after
merged x86 SIMD model prerequisites.
CTR encrypts six lanes using xmm0..5, round key xmm6, and load temporary xmm7.
The counter prefix is cached in scratch; each lane inserts its incremented low
word with MOVD/PSLLDQ/POR. The final low word is stored once. Only the low 32
bits wrap, as GCM requires; partial-store forwarding stalls are avoided.
-/
namespace VG.Impl.Aes.X86.AesNi
open VG.X86

def at_ (b : Reg) (d : Nat) : MemOp := { base := b, disp := d }
def argOp (i : Nat) : MemOp := at_ .esp (4 + 4 * i)

/-! ## Six-lane counter mode -/

/-- `eax` schedule, `ecx` rounds, `edx` counter, `esi` data, `edi` n,
`ebp` scratch, `ebx` counter low word as a big-endian integer.
Scratch [0,16) saves callee GPRs, [16,32) holds the prefix with its last word
zero; the immutable stack arguments supply the schedule pointer. -/
def savedRegs : List (Reg × Nat) := [(.ebx, 0), (.esi, 4), (.edi, 8), (.ebp, 12)]

def keyOp (regs : List XReg) (op : XBinOp) (off : Nat) : List Instr :=
  .movdquLoad .xmm6 (at_ .eax off) :: regs.map fun b => .xop (.bin op b .xmm6)

def round (regs : List XReg) (j : Nat) : List Instr := keyOp regs .aesenc (16 * j)

/-- Branches depend only on the public number of rounds. -/
def aes (regs : List XReg) : Prog isa :=
  .seq (.block (keyOp regs .pxor 0 ++ (List.range 9).flatMap (fun j => round regs (j + 1)) ++
      [.alu .cmp .ecx (.imm 10)]))
    (.ite .e (.block (keyOp regs .aesenclast 160))
      (.seq (.block (round regs 10 ++ round regs 11 ++ [.alu .cmp .ecx (.imm 12)]))
        (.ite .e (.block (keyOp regs .aesenclast 192))
          (.block (round regs 12 ++ round regs 13 ++ keyOp regs .aesenclast 224)))))

/-- Construct one lane from a numeric low word and the cached prefix in xmm7.
`eax` is a temporary here; the public schedule pointer is restored before AES. -/
def ctrs : List XReg → List Instr
  | [] => []
  | b :: bs => ([.mov .eax (.reg .ebx), .bswap .eax, .xop (.movd b .eax),
      .xop (.shift .pslldq b 12), .xop (.bin .por b .xmm7),
      .alu .add .ebx (.imm 1)] : List Instr) ++ ctrs bs

/-- The prefix survives in scratch; reload the schedule from immutable arguments. -/
def ctrLoad (regs : List XReg) : List Instr :=
  ([.movdquLoad .xmm7 (at_ .ebp 16)] : List Instr) ++ ctrs regs ++
  ([.mov .eax (.mem (argOp 0))] : List Instr)

def xorData : List XReg → Nat → List Instr
  | [], _ => []
  | b :: bs, j => [.movdquLoad .xmm7 (at_ .esi (16 * j)), .xop (.bin .pxor b .xmm7),
      .movdquStore (at_ .esi (16 * j)) b] ++ xorData bs (j + 1)

def regs6 : List XReg := [.xmm0, .xmm1, .xmm2, .xmm3, .xmm4, .xmm5]

def body6 : Prog isa :=
  .seq (.block (ctrLoad regs6)) (.seq (aes regs6)
    (.block (xorData regs6 0 ++ [.alu .add .esi (.imm 96), .alu .sub .edi (.imm 6),
      .alu .cmp .edi (.imm 6)])))

def body1 : Prog isa :=
  .seq (.block (ctrLoad [.xmm0])) (.seq (aes [.xmm0])
    (.block (xorData [.xmm0] 0 ++ [.alu .add .esi (.imm 16), .alu .sub .edi (.imm 1)])))

def prologue : List Instr :=
  [.mov .eax (.mem (argOp 5))] ++ savedRegs.map (fun (r, d) => .store (at_ .eax d) r) ++
  [.mov .ebp (.reg .eax), .mov .eax (.mem (argOp 0)), .mov .ecx (.mem (argOp 1)),
   .mov .edx (.mem (argOp 2)), .mov .esi (.mem (argOp 3)), .mov .edi (.mem (argOp 4)),
   .mov .ebx (.mem (at_ .edx 12)), .bswap .ebx,
   .movdquLoad .xmm7 (at_ .edx 0), .xop (.shift .pslldq .xmm7 4),
   .xop (.shift .psrldq .xmm7 4), .movdquStore (at_ .ebp 16) .xmm7,
   .alu .cmp .edi (.imm 6)]

def restore : List Instr :=
  [.mov .eax (.reg .ebx), .bswap .eax, .store (at_ .edx 12) .eax,
   .mov .ebx (.mem (at_ .ebp 0)), .mov .esi (.mem (at_ .ebp 4)),
   .mov .edi (.mem (at_ .ebp 8)), .mov .ebp (.mem (at_ .ebp 12))]

def ctr32 : Prog isa :=
  .seq (.block prologue)
    (.seq (.ite .b (.block []) (.loop body6 .ae))
      (.seq (.block [.alu .test .edi (.reg .edi)])
        (.seq (.ite .e (.block []) (.loop body1 .ne)) (.block restore))))

end VG.Impl.Aes.X86.AesNi
