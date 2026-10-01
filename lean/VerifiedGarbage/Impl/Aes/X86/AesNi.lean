import VerifiedGarbage.Spec.Aes
import VerifiedGarbage.TCB.X86.Isa

/-!
Draft 32-bit AES-NI implementation. Not registered or proven; only usable after
merged x86 SIMD model prerequisites. Key expansion uses only caller-saved GPRs.
CTR encrypts six lanes using xmm0..5, round key xmm6, and load temporary xmm7.
The counter prefix is cached in scratch; each lane inserts its incremented low
word with MOVD/PSLLDQ/POR. The final low word is stored once. Only the low 32
bits wrap, as GCM requires; partial-store forwarding stalls are avoided.
-/
namespace VG.Impl.Aes.X86.AesNi
open VG.X86

def at_ (b : Reg) (d : Nat) : MemOp := { base := b, disp := d }
def argOp (i : Nat) : MemOp := at_ .esp (4 + 4 * i)

/-! ## Key expansion -/

/-- The round constant `Rcon[j]`'s first byte, `x^(j−1)` (FIPS 197 §5.2). -/
def rc (j : Nat) : BitVec 8 := Nat.repeat Spec.Aes.xtimes (j - 1) 1

/-- `d ← prefixXor(d) ⊕ bcast(dword sel of aeskeygenassist(s, r))`, then
store `d` at `schedule + off`. `xmm3` and `xmm4` are temporaries. -/
def kstep (d s : XReg) (sel r : BitVec 8) (off : Nat) : List Instr :=
  [.xop (.aeskeygenassist .xmm3 s r), .xop (.pshufd .xmm3 .xmm3 sel),
   .xop (.bin .movdqa .xmm4 d),
   .xop (.shift .pslldq .xmm4 4), .xop (.bin .pxor d .xmm4),
   .xop (.shift .pslldq .xmm4 4), .xop (.bin .pxor d .xmm4),
   .xop (.shift .pslldq .xmm4 4), .xop (.bin .pxor d .xmm4),
   .xop (.bin .pxor d .xmm3),
   .movdquStore (at_ .edx off) d]

/-- For `Nk = 6`: `B ← [b₀, b₀ ⊕ b₁, …] ⊕ bcast(a₃)` (`A` in `xmm1`, `B` in
`xmm2`), then store `B` at `schedule + off`. -/
def kstepB6 (off : Nat) : List Instr :=
  [.xop (.pshufd .xmm3 .xmm1 0xff), .xop (.bin .movdqa .xmm4 .xmm2),
   .xop (.shift .pslldq .xmm4 4), .xop (.bin .pxor .xmm2 .xmm4),
   .xop (.bin .pxor .xmm2 .xmm3),
   .movdquStore (at_ .edx off) .xmm2]

/-- AES-128: 11 round keys. -/
def expand128 : List Instr :=
  [.movdquLoad .xmm1 (at_ .eax 0), .movdquStore (at_ .edx 0) .xmm1] ++
  (List.range 10).flatMap fun k => kstep .xmm1 .xmm1 0xff (rc (k + 1)) (16 * (k + 1))

/-- AES-192: 13 round keys (52 words), 6 words at a time. -/
def expand192 : List Instr :=
  [.movdquLoad .xmm1 (at_ .eax 0), .movdquLoad .xmm2 (at_ .eax 8), .xop (.shift .psrldq .xmm2 8),
   .movdquStore (at_ .edx 0) .xmm1, .movdquStore (at_ .edx 16) .xmm2] ++
  (List.range 7).flatMap (fun k =>
    kstep .xmm1 .xmm2 0x55 (rc (k + 1)) (24 * (k + 1)) ++ kstepB6 (24 * (k + 1) + 16)) ++
  kstep .xmm1 .xmm2 0x55 (rc 8) 192

/-- AES-256: 15 round keys (60 words), 8 words at a time. -/
def expand256 : List Instr :=
  [.movdquLoad .xmm1 (at_ .eax 0), .movdquLoad .xmm2 (at_ .eax 16),
   .movdquStore (at_ .edx 0) .xmm1, .movdquStore (at_ .edx 16) .xmm2] ++
  (List.range 6).flatMap (fun k =>
    kstep .xmm1 .xmm2 0xff (rc (k + 1)) (32 * (k + 1)) ++
    kstep .xmm2 .xmm1 0xaa 0 (32 * (k + 1) + 16)) ++
  kstep .xmm1 .xmm2 0xff (rc 7) 224

def expandKey : Prog isa :=
  .seq (.block [.mov .eax (.mem (argOp 0)), .mov .ecx (.mem (argOp 1)),
      .mov .edx (.mem (argOp 2)), .alu .cmp .ecx (.imm 24)])
    (.ite .e (.block expand192)
      (.seq (.block [.alu .cmp .ecx (.imm 32)]) (.ite .e (.block expand256) (.block expand128))))

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
