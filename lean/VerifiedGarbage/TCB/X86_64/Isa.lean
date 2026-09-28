import VerifiedGarbage.TCB.Code

/-!
# x86-64 machine model

**Trusted.** A model of the subset of x86-64 used by our implementations.
Each instruction's semantics here must agree with the Intel SDM; when adding
an instruction, cite the SDM pseudocode it transcribes.

Modelling choices:
* Only 64-bit and 32-bit operand sizes are modelled, plus byte loads
  (`movzx`, zero-extending) and byte stores. SDM Vol. 1 §3.4.1.1: "32-bit
  operands generate a 32-bit result, zero-extended to a 64-bit result in the
  destination general-purpose register."
* Only CF, ZF, SF and OF are modelled. Each is an `Option Bool`; `none` means
  "undefined" (as the SDM specifies for some instructions). Evaluating a
  branch on an undefined flag faults, so verified code never depends on one.
  PF and AF are not modelled, and no modelled instruction reads them.
* Memory accesses must lie within the state's permitted regions: loads within
  `rd ++ wr`, stores within `wr`; otherwise the instruction faults.
* Instructions whose timing depends on their operands (e.g. `div`) must never
  be added: the constant-time leakage model assumes they do not exist.
* Calls (`call`) and returns (`ret`) are near and direct (SDM Vol. 2, "CALL",
  "RET"). The return addresses are the next of the state's `unknowns`,
  which nothing constrains (see `TCB/Code.lean`).
* The SSE registers `xmm0`–`xmm15` are modelled as 128 bits each (SDM Vol. 1
  §10.2.2), and the upper halves (bits 255:128) of the AVX registers
  `ymm0`–`ymm15` that alias them (SDM Vol. 1 §14.1.1) separately. Bits above
  255 (AVX-512) are not modelled: no modelled instruction reads them, and
  every VEX-encoded instruction here zeroes them. The legacy SSE instructions
  leave bits 255:128 unmodified; the VEX-encoded ones with 128-bit operands
  zero them (SDM Vol. 1 §14.1.3: "VEX.128 encoded … the upper bits (MAXVL-1:128)
  of the destination are zeroed"). No SSE or AVX instruction has a memory
  operand except the unaligned `movdqu`/`vmovdqu` loads and stores and
  `vbroadcasti128`, which (like every VEX memory operand but those of the
  aligned moves) need no alignment, so no alignment fault needs modelling.
* MXCSR (SDM Vol. 1 §10.2.3) is modelled as a 32-bit value that only
  `ldmxcsr` and `stmxcsr` access: no other modelled instruction reads or
  writes it (integer instructions raise no SIMD floating-point exceptions).
  Its control bits (15:6) are callee-saved (see `Target.lean`). `lfence`
  has no architectural effect, so the model treats it as a no-op.
* MXCSR-configuration-dependent timing (MCDT): on some Intel processors,
  `pmuludq` and `vpmuludq`, although on Intel's DOIT list, may take up to a
  cycle longer to retire for specific data values unless MXCSR holds
  `0x1FBF` (Intel, "MXCSR Configuration Dependent Timing"; the processors
  that enumerate `MCDT_NO`, CPUID.(EAX=7H,ECX=2):EDX[5], are not affected).
  The leakage model does not see this, so code must only give these two
  instructions secret operands between Intel's prologue and epilogue:
  `stmxcsr` (save the caller's MXCSR), `ldmxcsr` of `0x1FBF`, `lfence`, then
  the code that uses them, then `lfence` and `ldmxcsr` of the saved value.
  Reviewers of an implementation check this; `lfence` and the MXCSR
  instructions exist in the model for it.
-/

namespace VG.X86_64

inductive Reg
  | rax | rcx | rdx | rbx | rsp | rbp | rsi | rdi
  | r8 | r9 | r10 | r11 | r12 | r13 | r14 | r15
  deriving DecidableEq, Repr, Inhabited

/-- The SSE registers. -/
inductive XReg
  | xmm0 | xmm1 | xmm2 | xmm3 | xmm4 | xmm5 | xmm6 | xmm7
  | xmm8 | xmm9 | xmm10 | xmm11 | xmm12 | xmm13 | xmm14 | xmm15
  deriving DecidableEq, Repr, Inhabited

structure State where
  gpr : Reg → BitVec 64
  cf : Option Bool
  zf : Option Bool
  sf : Option Bool
  of : Option Bool
  /-- The low 128 bits of each SSE register. -/
  xmm : XReg → BitVec 128 := fun _ => 0
  /-- Bits 255:128 of each AVX register. -/
  ymmHi : XReg → BitVec 128 := fun _ => 0
  /-- The SSE control and status register (SDM Vol. 1 §10.2.3). -/
  mxcsr : BitVec 32 := 0x1F80
  mem : Mem
  /-- Regions the code may read (in addition to `wr`). -/
  rd : List Region
  /-- Regions the code may read and write. -/
  wr : List Region
  /-- Values the model does not know, used in order: the return address each
  call stores and, on the ARM targets, what a linker veneer may leave in the
  intra-procedure-call scratch registers (see `TCB/Code.lean`). -/
  unknowns : Nat → BitVec 64 := fun _ => 0

/-- A memory operand `[base + index * scale + disp]`. -/
structure MemOp where
  base : Reg
  index : Option Reg := none
  /-- 1, 2, 4 or 8. -/
  scale : Nat := 1
  disp : Int := 0
  deriving DecidableEq, Repr

inductive Src
  | reg (r : Reg)
  /-- A 32-bit immediate, sign-extended to 64 bits. -/
  | imm (v : BitVec 32)
  | mem (m : MemOp)
  deriving DecidableEq, Repr

inductive AluOp | add | adc | sub | sbb | and | or | xor | cmp | test
  deriving DecidableEq, Repr

/-- Shifts and rotates by an immediate count. -/
inductive ShiftOp | ror | shr
  deriving DecidableEq, Repr

/-- Two-operand SSE instructions `op xmm1, xmm2` (register forms only). -/
inductive XBinOp
  | movdqa | paddd | pxor | por | punpckldq | punpckhdq | punpcklqdq | punpckhqdq
  | pshufb | sha256msg1 | sha256msg2
  | pand | pandn | paddq | pmuludq
  | aesenc | aesenclast | aesdec | aesdeclast | aesimc
  deriving DecidableEq, Repr

/-- SSE2 shifts by an immediate count: of each doubleword (`pslld`, `psrld`),
of each quadword (`psllq`, `psrlq`), or of the whole register by bytes
(`pslldq`, `psrldq`). -/
inductive XShiftOp | pslld | psrld | psllq | psrlq | pslldq | psrldq
  deriving DecidableEq, Repr

/-- The vector length of a VEX-encoded instruction: 128 bits (`xmm`
operands, `VEX.L = 0`) or 256 bits (`ymm` operands, `VEX.L = 1`). -/
inductive VLen | l128 | l256
  deriving DecidableEq, Repr

/-- VEX-encoded three-operand instructions `vop dst, src1, src2` that act on
each 128-bit lane as the legacy SSE instruction does on its destination
(`src1`) and source (`src2`). -/
inductive VBinOp
  | vpaddd | vpaddq | vpxor | vpor | vpand | vpandn | vpshufb | vpmuludq
  | vpunpckldq | vpunpckhdq | vpunpcklqdq | vpunpckhqdq
  deriving DecidableEq, Repr

/-- AVX2 shifts of each element by the count in the corresponding element
of a register. -/
inductive VVarOp | vpsllvd | vpsrlvd | vpsllvq | vpsrlvq
  deriving DecidableEq, Repr

/-- SSE instructions that write only an SSE register. -/
inductive XOp
  /-- `op xmm1, xmm2` -/
  | bin (op : XBinOp) (dst src : XReg)
  /-- `op xmm1, imm8` -/
  | shift (op : XShiftOp) (dst : XReg) (count : BitVec 8)
  /-- `pshufd xmm1, xmm2, imm8` -/
  | pshufd (dst src : XReg) (order : BitVec 8)
  /-- `palignr xmm1, xmm2, imm8` -/
  | palignr (dst src : XReg) (shift : BitVec 8)
  /-- `sha256rnds2 xmm1, xmm2, xmm0` (`xmm0` is implicit in the encoding) -/
  | sha256rnds2 (dst src : XReg)
  /-- `movq xmm, r64` (`66 REX.W 0F 6E /r`) -/
  | movq (dst : XReg) (src : Reg)
  /-- `aeskeygenassist xmm1, xmm2, imm8` -/
  | aeskeygenassist (dst src : XReg) (rcon : BitVec 8)
  /-- `pclmulqdq xmm1, xmm2, imm8` -/
  | pclmulqdq (dst src : XReg) (sel : BitVec 8)
  deriving DecidableEq, Repr

/-- AVX instructions that write only vector registers. -/
inductive VOp
  /-- `vop dst, src1, src2` -/
  | vbin (op : VBinOp) (len : VLen) (dst src1 src2 : XReg)
  /-- `vmovdqa dst, src` -/
  | vmovdqa (len : VLen) (dst src : XReg)
  /-- `vop dst, src, imm8` (`vpslld`, `vpsrld`, `vpsllq`, `vpsrlq`, `vpslldq`,
  `vpsrldq`) -/
  | vshift (op : XShiftOp) (len : VLen) (dst src : XReg) (count : BitVec 8)
  /-- `vpshufd dst, src, imm8` -/
  | vpshufd (len : VLen) (dst src : XReg) (order : BitVec 8)
  /-- `vpalignr dst, src1, src2, imm8` -/
  | vpalignr (len : VLen) (dst src1 src2 : XReg) (shift : BitVec 8)
  /-- `vpblendd dst, src1, src2, imm8` -/
  | vpblendd (len : VLen) (dst src1 src2 : XReg) (sel : BitVec 8)
  /-- `vop dst, src1, src2` (`vpsllvd`, `vpsrlvd`, `vpsllvq`, `vpsrlvq`) -/
  | vvar (op : VVarOp) (len : VLen) (dst src1 src2 : XReg)
  /-- `vpbroadcastd dst, xmm` -/
  | vpbroadcastd (len : VLen) (dst src : XReg)
  /-- `vpbroadcastq dst, xmm` -/
  | vpbroadcastq (len : VLen) (dst src : XReg)
  /-- `vpermq ymm1, ymm2, imm8` -/
  | vpermq (dst src : XReg) (order : BitVec 8)
  /-- `vperm2i128 ymm1, ymm2, ymm3, imm8` -/
  | vperm2i128 (dst src1 src2 : XReg) (sel : BitVec 8)
  /-- `vinserti128 ymm1, ymm2, xmm3, imm8` -/
  | vinserti128 (dst src1 src2 : XReg) (sel : BitVec 8)
  /-- `vextracti128 xmm1, ymm2, imm8` -/
  | vextracti128 (dst src : XReg) (sel : BitVec 8)
  /-- `vmovq xmm, r64` (`VEX.128.66.0F.W1 6E /r`) -/
  | vmovq (dst : XReg) (src : Reg)
  /-- `vzeroupper` -/
  | vzeroupper
  deriving DecidableEq, Repr

inductive Instr
  /-- `mov dst, src` (64-bit) -/
  | mov (dst : Reg) (src : Src)
  /-- `mov QWORD PTR [dst], src` -/
  | store (dst : MemOp) (src : Reg)
  /-- Two-operand ALU instruction `op dst, src` (64-bit). -/
  | alu (op : AluOp) (dst : Reg) (src : Src)
  /-- `mov r32, src` (32-bit; `DWORD PTR` for a memory source). An immediate
  is used as is. The result is zero-extended into the 64-bit register. -/
  | mov32 (dst : Reg) (src : Src)
  /-- `mov DWORD PTR [dst], r32` -/
  | store32 (dst : MemOp) (src : Reg)
  /-- Two-operand ALU instruction `op r32, src` (32-bit; `DWORD PTR` for a
  memory source). An immediate is used as is. -/
  | alu32 (op : AluOp) (dst : Reg) (src : Src)
  /-- `op r32, count` (32-bit) with an immediate count. Only counts `1 ≤ count ≤ 31`
  are modelled; any other count faults. -/
  | shift32 (op : ShiftOp) (dst : Reg) (count : Nat)
  /-- `bswap r32` -/
  | bswap32 (dst : Reg)
  /-- `movzx r32, BYTE PTR [src]`: the byte, zero-extended into the 64-bit register. -/
  | movzx8 (dst : Reg) (src : MemOp)
  /-- `mov BYTE PTR [dst], r8`: the low byte of `src`. -/
  | store8 (dst : MemOp) (src : Reg)
  /-- `bswap r64` -/
  | bswap (dst : Reg)
  /-- `op r64, count` (64-bit) with an immediate count. Only counts `1 ≤ count ≤ 63`
  are modelled; any other count faults. -/
  | shift (op : ShiftOp) (dst : Reg) (count : Nat)
  /-- `movabs r64, imm64`: `MOV r64, imm64` (REX.W + B8+rd io), a full 64-bit
  immediate. -/
  | movImm64 (dst : Reg) (v : BitVec 64)
  /-- `movdqu xmm, XMMWORD PTR [src]` (`F3 0F 6F /r`) -/
  | movdquLoad (dst : XReg) (src : MemOp)
  /-- `movdqu XMMWORD PTR [dst], xmm` (`F3 0F 7F /r`) -/
  | movdquStore (dst : MemOp) (src : XReg)
  /-- An SSE instruction that writes only an SSE register. -/
  | xop (op : XOp)
  /-- An AVX instruction that writes only vector registers. -/
  | vop (op : VOp)
  /-- `vmovdqu xmm, XMMWORD PTR [src]` (`VEX.128.F3.0F.WIG 6F /r`) or
  `vmovdqu ymm, YMMWORD PTR [src]` (`VEX.256.F3.0F.WIG 6F /r`) -/
  | vmovdquLoad (len : VLen) (dst : XReg) (src : MemOp)
  /-- `vmovdqu XMMWORD PTR [dst], xmm` (`VEX.128.F3.0F.WIG 7F /r`) or
  `vmovdqu YMMWORD PTR [dst], ymm` (`VEX.256.F3.0F.WIG 7F /r`) -/
  | vmovdquStore (len : VLen) (dst : MemOp) (src : XReg)
  /-- `vbroadcasti128 ymm, XMMWORD PTR [src]` (`VEX.256.66.0F38.W0 5A /r`) -/
  | vbroadcasti128 (dst : XReg) (src : MemOp)
  /-- `stmxcsr DWORD PTR [dst]` (`NP 0F AE /3`) -/
  | stmxcsr (dst : MemOp)
  /-- `ldmxcsr DWORD PTR [src]` (`NP 0F AE /2`) -/
  | ldmxcsr (src : MemOp)
  /-- `lfence` (`NP 0F AE E8`) -/
  | lfence
  deriving DecidableEq, Repr

/-- Branch conditions (`jcc` suffixes). -/
inductive Cond
  /-- `je`: ZF = 1 -/
  | e
  /-- `jne`: ZF = 0 -/
  | ne
  /-- `jb`: CF = 1 -/
  | b
  /-- `jae`: CF = 0 -/
  | ae
  deriving DecidableEq, Repr

namespace State

def setReg (s : State) (r : Reg) (v : BitVec 64) : State :=
  { s with gpr := fun r' => if r' = r then v else s.gpr r' }

/-- Effective address of a memory operand. -/
def ea (s : State) (m : MemOp) : Addr :=
  match m.index with
  | none => s.gpr m.base + BitVec.ofInt 64 m.disp
  | some i => s.gpr m.base + s.gpr i * BitVec.ofNat 64 m.scale + BitVec.ofInt 64 m.disp

/-- Load 8 bytes, faulting if not permitted. -/
def load64 (s : State) (a : Addr) : Option (BitVec 64) :=
  if InRegions (s.rd ++ s.wr) a 8 then some (s.mem.readW a 64) else none

/-- Store 8 bytes, faulting if not permitted. -/
def store64 (s : State) (a : Addr) (v : BitVec 64) : Option State :=
  if InRegions s.wr a 8 then some { s with mem := s.mem.writeW a v } else none

/-- Load 4 bytes, faulting if not permitted. -/
def load32 (s : State) (a : Addr) : Option (BitVec 32) :=
  if InRegions (s.rd ++ s.wr) a 4 then some (s.mem.readW a 32) else none

/-- Store 4 bytes, faulting if not permitted. -/
def store32 (s : State) (a : Addr) (v : BitVec 32) : Option State :=
  if InRegions s.wr a 4 then some { s with mem := s.mem.writeW a v } else none

/-- Load 1 byte, faulting if not permitted. -/
def load8 (s : State) (a : Addr) : Option Byte :=
  if InRegions (s.rd ++ s.wr) a 1 then some (s.mem a) else none

/-- Store 1 byte, faulting if not permitted. -/
def store8 (s : State) (a : Addr) (v : Byte) : Option State :=
  if InRegions s.wr a 1 then some { s with mem := s.mem.writeW a v } else none

/-- Load 16 bytes, faulting if not permitted. -/
def load128 (s : State) (a : Addr) : Option (BitVec 128) :=
  if InRegions (s.rd ++ s.wr) a 16 then some (s.mem.readW a 128) else none

/-- Store 16 bytes, faulting if not permitted. -/
def store128 (s : State) (a : Addr) (v : BitVec 128) : Option State :=
  if InRegions s.wr a 16 then some { s with mem := s.mem.writeW a v } else none

def setXmm (s : State) (r : XReg) (v : BitVec 128) : State :=
  { s with xmm := fun r' => if r' = r then v else s.xmm r' }

/-- Load 32 bytes, faulting if not permitted. -/
def load256 (s : State) (a : Addr) : Option (BitVec 256) :=
  if InRegions (s.rd ++ s.wr) a 32 then some (s.mem.readW a 256) else none

/-- Store 32 bytes, faulting if not permitted. -/
def store256 (s : State) (a : Addr) (v : BitVec 256) : Option State :=
  if InRegions s.wr a 32 then some { s with mem := s.mem.writeW a v } else none

/-- Lane `i` (bits `128i+127:128i`, for `i` 0 or 1) of an AVX register. -/
def lane (s : State) (r : XReg) (i : Nat) : BitVec 128 := if i = 0 then s.xmm r else s.ymmHi r

/-- The 256 bits of an AVX register. -/
def ymm (s : State) (r : XReg) : BitVec 256 := s.ymmHi r ++ s.xmm r

/-- Write a VEX-encoded instruction's result to `r`: lane 0 is `lo`, and
lane 1 is `hi` for 256-bit operands and 0 for 128-bit ones (SDM Vol. 1
§14.1.3). -/
def setV (s : State) (len : VLen) (r : XReg) (lo hi : BitVec 128) : State :=
  { s with
    xmm := fun r' => if r' = r then lo else s.xmm r'
    ymmHi := fun r' => if r' = r then (match len with | .l128 => 0 | .l256 => hi) else s.ymmHi r' }

/-- Write a 32-bit result, zero-extended to 64 bits (SDM Vol. 1 §3.4.1.1). -/
def setReg32 (s : State) (r : Reg) (v : BitVec 32) : State := s.setReg r (v.setWidth 64)

/-- Set CF, OF, ZF and SF. -/
def setFlags (s : State) (cf of zf sf : Option Bool) : State :=
  { s with cf := cf, of := of, zf := zf, sf := sf }

end State

/-- Read a source operand. Immediates are sign-extended from 32 bits. -/
def readSrc (s : State) : Src → Option (BitVec 64)
  | .reg r => some (s.gpr r)
  | .imm v => some (v.signExtend 64)
  | .mem m => s.load64 (s.ea m)

/-- Read a 32-bit source operand: the low 32 bits of a register, the
immediate itself, or 4 bytes of memory. -/
def readSrc32 (s : State) : Src → Option (BitVec 32)
  | .reg r => some ((s.gpr r).setWidth 32)
  | .imm v => some v
  | .mem m => s.load32 (s.ea m)

def srcAddrs (s : State) : Src → List Addr
  | .mem m => [s.ea m]
  | _ => []

/-- Flags after the result `r` of an arithmetic or logic operation with carry
`c` and signed overflow `o`: ZF and SF are computed from `r`. -/
def arithFlags {w : Nat} (s : State) (r : BitVec w) (c o : Bool) : State :=
  s.setFlags (some c) (some o) (some (r == 0)) (some r.msb)

/-- Signed overflow of `a + b (+ carry) = r`. -/
def addOverflow {w : Nat} (a b r : BitVec w) : Bool := a.msb == b.msb && r.msb != a.msb
/-- Signed overflow of `a - b (- borrow) = r`. -/
def subOverflow {w : Nat} (a b r : BitVec w) : Bool := a.msb != b.msb && r.msb != a.msb

/-- SDM Vol. 2: ADD, ADC, SUB, SBB, CMP set CF/OF/ZF/SF by the result; AND,
OR, XOR, TEST clear CF and OF and set ZF/SF by the result. -/
def execAlu (op : AluOp) (dst : Reg) (src : Src) (s : State) : Option State :=
  (readSrc s src).bind fun b =>
  let a := s.gpr dst
  match op with
  | .add => let r := a + b
    some ((arithFlags s r (2 ^ 64 ≤ a.toNat + b.toNat) (addOverflow a b r)).setReg dst r)
  | .adc => s.cf.map fun c =>
    let r := a + b + (BitVec.ofBool c).setWidth 64
    (arithFlags s r (2 ^ 64 ≤ a.toNat + b.toNat + c.toNat) (addOverflow a b r)).setReg dst r
  | .sub => let r := a - b
    some ((arithFlags s r (a.toNat < b.toNat) (subOverflow a b r)).setReg dst r)
  | .sbb => s.cf.map fun c =>
    let r := a - b - (BitVec.ofBool c).setWidth 64
    (arithFlags s r (a.toNat < b.toNat + c.toNat) (subOverflow a b r)).setReg dst r
  | .cmp => let r := a - b
    some (arithFlags s r (a.toNat < b.toNat) (subOverflow a b r))
  | .and => let r := a &&& b; some ((arithFlags s r false false).setReg dst r)
  | .or => let r := a ||| b; some ((arithFlags s r false false).setReg dst r)
  | .xor => let r := a ^^^ b; some ((arithFlags s r false false).setReg dst r)
  | .test => let r := a &&& b; some (arithFlags s r false false)

/-- The 32-bit forms of `execAlu`: the same operations on the low 32 bits,
with the flags computed from the 32-bit result. CMP and TEST write no
register; every other operation zero-extends its result (SDM Vol. 1 §3.4.1.1). -/
def execAlu32 (op : AluOp) (dst : Reg) (src : Src) (s : State) : Option State :=
  (readSrc32 s src).bind fun b =>
  let a := (s.gpr dst).setWidth 32
  match op with
  | .add => let r := a + b
    some ((arithFlags s r (2 ^ 32 ≤ a.toNat + b.toNat) (addOverflow a b r)).setReg32 dst r)
  | .adc => s.cf.map fun c =>
    let r := a + b + (BitVec.ofBool c).setWidth 32
    (arithFlags s r (2 ^ 32 ≤ a.toNat + b.toNat + c.toNat) (addOverflow a b r)).setReg32 dst r
  | .sub => let r := a - b
    some ((arithFlags s r (a.toNat < b.toNat) (subOverflow a b r)).setReg32 dst r)
  | .sbb => s.cf.map fun c =>
    let r := a - b - (BitVec.ofBool c).setWidth 32
    (arithFlags s r (a.toNat < b.toNat + c.toNat) (subOverflow a b r)).setReg32 dst r
  | .cmp => let r := a - b
    some (arithFlags s r (a.toNat < b.toNat) (subOverflow a b r))
  | .and => let r := a &&& b; some ((arithFlags s r false false).setReg32 dst r)
  | .or => let r := a ||| b; some ((arithFlags s r false false).setReg32 dst r)
  | .xor => let r := a ^^^ b; some ((arithFlags s r false false).setReg32 dst r)
  | .test => let r := a &&& b; some (arithFlags s r false false)

/-- SDM Vol. 2, "RCL/RCR/ROL/ROR" and "SAL/SAR/SHL/SHR", for a 32-bit
operand and a count `n` with `1 ≤ n ≤ 31` (so the masked count `n AND 1FH`
is `n`; other counts fault):

* ROR: the operand is rotated right by `n`; CF := MSB of the result; OF :=
  MSB XOR MSB−1 of the result if `n = 1`, otherwise undefined; SF and ZF are
  unaffected.
* SHR: the operand is shifted right (logically) by `n`; CF := the last bit
  shifted out (bit `n − 1` of the operand); OF := MSB of the original operand
  if `n = 1`, otherwise undefined; SF and ZF are set according to the result.

(AF and PF are not modelled.) -/
def execShift32 (op : ShiftOp) (dst : Reg) (n : Nat) (s : State) : Option State :=
  if 1 ≤ n ∧ n ≤ 31 then
    let a := (s.gpr dst).setWidth 32
    match op with
    | .ror => let r := a.rotateRight n
      some ((s.setFlags (some r.msb) (if n = 1 then some (r.msb ^^ r.getMsbD 1) else none)
        s.zf s.sf).setReg32 dst r)
    | .shr => let r := a >>> n
      some ((s.setFlags (some (a.getLsbD (n - 1))) (if n = 1 then some a.msb else none)
        (some (r == 0)) (some r.msb)).setReg32 dst r)
  else none

/-- SDM Vol. 2, "BSWAP": `DEST[7:0] := TEMP[31:24]; DEST[15:8] := TEMP[23:16];
DEST[23:16] := TEMP[15:8]; DEST[31:24] := TEMP[7:0]` for a 32-bit operand
(zero-extended, SDM Vol. 1 §3.4.1.1). No flags are affected. -/
def bswap32 (a : BitVec 32) : BitVec 32 :=
  a.extractLsb' 0 8 ++ a.extractLsb' 8 8 ++ a.extractLsb' 16 8 ++ a.extractLsb' 24 8

/-- The 64-bit form of `execShift32` (the same SDM pseudocode), for a count
`n` with `1 ≤ n ≤ 63` (so the masked count `n AND 3FH` is `n`; other counts
fault):

* ROR: the operand is rotated right by `n`; CF := MSB of the result; OF :=
  MSB XOR MSB−1 of the result if `n = 1`, otherwise undefined; SF and ZF are
  unaffected.
* SHR: the operand is shifted right (logically) by `n`; CF := the last bit
  shifted out (bit `n − 1` of the operand); OF := MSB of the original operand
  if `n = 1`, otherwise undefined; SF and ZF are set according to the result.

(AF and PF are not modelled.) -/
def execShift (op : ShiftOp) (dst : Reg) (n : Nat) (s : State) : Option State :=
  if 1 ≤ n ∧ n ≤ 63 then
    let a := s.gpr dst
    match op with
    | .ror => let r := a.rotateRight n
      some ((s.setFlags (some r.msb) (if n = 1 then some (r.msb ^^ r.getMsbD 1) else none)
        s.zf s.sf).setReg dst r)
    | .shr => let r := a >>> n
      some ((s.setFlags (some (a.getLsbD (n - 1))) (if n = 1 then some a.msb else none)
        (some (r == 0)) (some r.msb)).setReg dst r)
  else none

/-- SDM Vol. 2, "BSWAP", for a 64-bit operand: `DEST[7:0] := TEMP[63:56];
DEST[15:8] := TEMP[55:48]; DEST[23:16] := TEMP[47:40]; DEST[31:24] :=
TEMP[39:32]; DEST[39:32] := TEMP[31:24]; DEST[47:40] := TEMP[23:16];
DEST[55:48] := TEMP[15:8]; DEST[63:56] := TEMP[7:0]`. No flags are affected. -/
def bswap64 (a : BitVec 64) : BitVec 64 :=
  a.extractLsb' 0 8 ++ a.extractLsb' 8 8 ++ a.extractLsb' 16 8 ++ a.extractLsb' 24 8 ++
    a.extractLsb' 32 8 ++ a.extractLsb' 40 8 ++ a.extractLsb' 48 8 ++ a.extractLsb' 56 8

/-! ### SSE

The SDM's pseudocode numbers bits from the least significant: doubleword `i`
of a 128-bit operand is bits `32i+31:32i`, quadword `i` bits `64i+63:64i`. -/

/-- Doubleword `i` of `x`: bits `32i+31:32i`. -/
def dword (x : BitVec 128) (i : Nat) : BitVec 32 := x.extractLsb' (32 * i) 32

/-- Quadword `i` of `x`: bits `64i+63:64i`. -/
def qword (x : BitVec 128) (i : Nat) : BitVec 64 := x.extractLsb' (64 * i) 64

/-- The 128-bit value with doublewords `d0` (bits 31:0), `d1`, `d2`, `d3` (bits 127:96). -/
def ofDwords (d0 d1 d2 d3 : BitVec 32) : BitVec 128 := d3 ++ d2 ++ d1 ++ d0

/-- Byte `i` of `x`: bits `8i+7:8i`. -/
def byte (x : BitVec 128) (i : Nat) : BitVec 8 := x.extractLsb' (8 * i) 8

/-- The 128-bit value whose byte `i` (bits `8i+7:8i`) is `f i`. -/
def ofBytes (f : Nat → BitVec 8) : BitVec 128 :=
  f 15 ++ f 14 ++ f 13 ++ f 12 ++ f 11 ++ f 10 ++ f 9 ++ f 8 ++
    f 7 ++ f 6 ++ f 5 ++ f 4 ++ f 3 ++ f 2 ++ f 1 ++ f 0

/-! The SHA-256 functions used, but not defined, by the SDM's pseudocode for
the SHA extensions: those of the SHA-256 standard, FIPS 180-4 §4.1.2, where
`ROTRⁿ` is a 32-bit rotate right and `SHRⁿ` a logical shift right. -/

/-- `Ch(x, y, z) = (x ∧ y) ⊕ (¬x ∧ z)` -/
def sha256Ch (x y z : BitVec 32) : BitVec 32 := (x &&& y) ^^^ (~~~x &&& z)

/-- `Maj(x, y, z) = (x ∧ y) ⊕ (x ∧ z) ⊕ (y ∧ z)` -/
def sha256Maj (x y z : BitVec 32) : BitVec 32 := (x &&& y) ^^^ (x &&& z) ^^^ (y &&& z)

/-- `Σ0(x) = ROTR²(x) ⊕ ROTR¹³(x) ⊕ ROTR²²(x)` -/
def sha256BigSigma0 (x : BitVec 32) : BitVec 32 :=
  x.rotateRight 2 ^^^ x.rotateRight 13 ^^^ x.rotateRight 22

/-- `Σ1(x) = ROTR⁶(x) ⊕ ROTR¹¹(x) ⊕ ROTR²⁵(x)` -/
def sha256BigSigma1 (x : BitVec 32) : BitVec 32 :=
  x.rotateRight 6 ^^^ x.rotateRight 11 ^^^ x.rotateRight 25

/-- `σ0(x) = ROTR⁷(x) ⊕ ROTR¹⁸(x) ⊕ SHR³(x)` -/
def sha256Sigma0 (x : BitVec 32) : BitVec 32 := x.rotateRight 7 ^^^ x.rotateRight 18 ^^^ x >>> 3

/-- `σ1(x) = ROTR¹⁷(x) ⊕ ROTR¹⁹(x) ⊕ SHR¹⁰(x)` -/
def sha256Sigma1 (x : BitVec 32) : BitVec 32 :=
  x.rotateRight 17 ^^^ x.rotateRight 19 ^^^ x >>> 10

/-- SDM Vol. 2, "SHA256MSG2": `W14 := SRC2[95:64]; W15 := SRC2[127:96];
W16 := SRC1[31:0] + σ1(W14); W17 := SRC1[63:32] + σ1(W15); W18 :=
SRC1[95:64] + σ1(W16); W19 := SRC1[127:96] + σ1(W17); DEST[127:96] := W19;
DEST[95:64] := W18; DEST[63:32] := W17; DEST[31:0] := W16`. -/
def sha256Msg2 (src1 src2 : BitVec 128) : BitVec 128 :=
  let w14 := dword src2 2
  let w15 := dword src2 3
  let w16 := dword src1 0 + sha256Sigma1 w14
  let w17 := dword src1 1 + sha256Sigma1 w15
  let w18 := dword src1 2 + sha256Sigma1 w16
  let w19 := dword src1 3 + sha256Sigma1 w17
  ofDwords w16 w17 w18 w19

/-! The AES transformations used, but not defined, by the SDM's pseudocode
for the AES instructions: those of the AES standard, FIPS 197 (§4 and §5).
The state `s[r, c]` (FIPS 197 §3.4) is byte `r + 4c` of the 128-bit operand,
so the operand is the state's 16 bytes in memory order. -/

/-- FIPS 197 §4.2, `XTIMES(b)`: `b` shifted left by one bit, XOR `{1b}` if the
bit shifted out was 1. -/
def aesXtimes (b : BitVec 8) : BitVec 8 := (b <<< 1) ^^^ (if b.msb then 0x1b else 0)

/-- FIPS 197 §4.2, the product `b • c` in GF(2⁸): the XOR of `XTIMES` applied
`i` times to `c`, for each bit `i` of `b` that is 1. -/
def aesMul (b c : BitVec 8) : BitVec 8 :=
  (List.range 8).foldl (fun acc i => if b.getLsbD i then acc ^^^ Nat.repeat aesXtimes i c else acc) 0

/-- FIPS 197 §4.4, the inverse `b⁻¹ = b²⁵⁴` in GF(2⁸), with `{00} ↦ {00}`:
`b^254 = b^2 • b^4 • … • b^128`, by repeated squaring. -/
def aesInv (b : BitVec 8) : BitVec 8 :=
  ((List.range 7).foldl (fun (acc, sq) _ => let sq := aesMul sq sq; (aesMul acc sq, sq))
    ((1 : BitVec 8), b)).1

/-- The byte whose bit `i` is `f i`. -/
def ofBits8 (f : Nat → Bool) : BitVec 8 :=
  BitVec.ofNat 8 ((List.range 8).foldl (fun acc i => acc + if f i then 2 ^ i else 0) 0)

/-- FIPS 197 §5.1.1, the S-box: `b ↦ b⁻¹`, then `b'ᵢ = bᵢ ⊕ b₍ᵢ₊₄₎ mod 8 ⊕
b₍ᵢ₊₅₎ mod 8 ⊕ b₍ᵢ₊₆₎ mod 8 ⊕ b₍ᵢ₊₇₎ mod 8 ⊕ cᵢ` with `c = {63}`. -/
def aesSbox (b : BitVec 8) : BitVec 8 :=
  let b := aesInv b
  let c : BitVec 8 := 0x63
  ofBits8 fun i => b.getLsbD i ^^ b.getLsbD ((i + 4) % 8) ^^ b.getLsbD ((i + 5) % 8) ^^
    b.getLsbD ((i + 6) % 8) ^^ b.getLsbD ((i + 7) % 8) ^^ c.getLsbD i

/-- FIPS 197 §5.3.2, the inverse S-box: the inverse of the affine
transformation, `b'ᵢ = b₍ᵢ₊₂₎ mod 8 ⊕ b₍ᵢ₊₅₎ mod 8 ⊕ b₍ᵢ₊₇₎ mod 8 ⊕ dᵢ` with
`d = {05}`, then `b ↦ b⁻¹`. -/
def aesInvSbox (b : BitVec 8) : BitVec 8 :=
  let d : BitVec 8 := 0x05
  aesInv (ofBits8 fun i =>
    b.getLsbD ((i + 2) % 8) ^^ b.getLsbD ((i + 5) % 8) ^^ b.getLsbD ((i + 7) % 8) ^^ d.getLsbD i)

/-- FIPS 197 §5.1.1 `SUBBYTES` and §5.3.2 `INVSUBBYTES`: `f` applied to every byte. -/
def aesMapBytes (f : BitVec 8 → BitVec 8) (x : BitVec 128) : BitVec 128 :=
  ofBytes fun i => f (byte x i)

/-- FIPS 197 §5.1.2 `SHIFTROWS`: `s'[r, c] = s[r, (c + r) mod 4]`. -/
def aesShiftRows (x : BitVec 128) : BitVec 128 :=
  ofBytes fun i => byte x (i % 4 + 4 * ((i / 4 + i % 4) % 4))

/-- FIPS 197 §5.3.1 `INVSHIFTROWS`: `s'[r, c] = s[r, (c − r) mod 4]`. -/
def aesInvShiftRows (x : BitVec 128) : BitVec 128 :=
  ofBytes fun i => byte x (i % 4 + 4 * ((i / 4 + 4 - i % 4) % 4))

/-- FIPS 197 §5.1.3 `MIXCOLUMNS` (with `m = [{02}, {03}, {01}, {01}]`) and
§5.3.3 `INVMIXCOLUMNS` (with `m = [{0e}, {0b}, {0d}, {09}]`):
`s'[r, c] = m₀ • s[r, c] ⊕ m₁ • s[r + 1, c] ⊕ m₂ • s[r + 2, c] ⊕ m₃ • s[r + 3, c]`,
rows modulo 4. -/
def aesMixWith (m₀ m₁ m₂ m₃ : BitVec 8) (x : BitVec 128) : BitVec 128 :=
  ofBytes fun i =>
    let a (k : Nat) : BitVec 8 := byte x ((i % 4 + k) % 4 + 4 * (i / 4))
    aesMul m₀ (a 0) ^^^ aesMul m₁ (a 1) ^^^ aesMul m₂ (a 2) ^^^ aesMul m₃ (a 3)

def aesMixColumns : BitVec 128 → BitVec 128 := aesMixWith 0x02 0x03 0x01 0x01

def aesInvMixColumns : BitVec 128 → BitVec 128 := aesMixWith 0x0e 0x0b 0x0d 0x09

/-- The carry-less product of two quadwords. SDM Vol. 2, "PCLMULQDQ", defines
bit `i` of the product as `TEMP1[0] AND TEMP2[i]` XOR … XOR `TEMP1[j] AND
TEMP2[i−j]` over all `j` with `0 ≤ i − j ≤ 63`, and bit 127 as 0; that is
the XOR, over the bits `j` of `a` that are 1, of `b` shifted left by `j`. -/
def clmul (a b : BitVec 64) : BitVec 128 :=
  (List.range 64).foldl (fun acc j => if a.getLsbD j then acc ^^^ (b.setWidth 128 <<< j) else acc) 0

/-- The result of `op dst, src`, given the old values `a` of `dst` and `b` of
`src`. SDM Vol. 2 (128-bit legacy SSE forms, which leave the destination's
bits above 127 unmodified; no flags are affected):

* MOVDQA: `DEST[127:0] := SRC[127:0]`.
* PADDD: `DEST[31:0] := DEST[31:0] + SRC[31:0]`, and likewise for doublewords
  1–3 (wrapping; no carry between doublewords).
* PXOR: `DEST := DEST XOR SRC`. POR: `DEST := DEST OR SRC`.
* PUNPCKLDQ (`INTERLEAVE_DWORDS`): `DEST[31:0] := SRC1[31:0]; DEST[63:32] :=
  SRC2[31:0]; DEST[95:64] := SRC1[63:32]; DEST[127:96] := SRC2[63:32]`.
* PUNPCKHDQ (`INTERLEAVE_HIGH_DWORDS`): `DEST[31:0] := SRC1[95:64];
  DEST[63:32] := SRC2[95:64]; DEST[95:64] := SRC1[127:96]; DEST[127:96] :=
  SRC2[127:96]`.
* PUNPCKLQDQ (`INTERLEAVE_QWORDS`): `DEST[63:0] := SRC1[63:0];
  DEST[127:64] := SRC2[63:0]`.
* PUNPCKHQDQ (`INTERLEAVE_HIGH_QWORDS`): `DEST[63:0] := SRC1[127:64];
  DEST[127:64] := SRC2[127:64]`.

* PSHUFB (with 128 bit operands): `TEMP := DEST; for i = 0 to 15 { if
  (SRC[(i * 8)+7] = 1) then DEST[(i*8)+7..(i*8)+0] := 0; else index[3..0] :=
  SRC[(i*8)+3 .. (i*8)+0]; DEST[(i*8)+7..(i*8)+0] :=
  TEMP[(index*8+7)..(index*8+0)]; endif }`.
* SHA256MSG1: `W4 := SRC2[31:0]; W3 := SRC1[127:96]; W2 := SRC1[95:64];
  W1 := SRC1[63:32]; W0 := SRC1[31:0]; DEST[127:96] := W3 + σ0(W4);
  DEST[95:64] := W2 + σ0(W3); DEST[63:32] := W1 + σ0(W2); DEST[31:0] :=
  W0 + σ0(W1)`.
* SHA256MSG2: see `sha256Msg2`.
* PAND: `DEST := DEST AND SRC`. PANDN: `DEST := NOT(DEST) AND SRC`.
* PADDQ: `DEST[63:0] := DEST[63:0] + SRC[63:0]; DEST[127:64] :=
  DEST[127:64] + SRC[127:64]` (wrapping).
* PMULUDQ: `DEST[63:0] := DEST[31:0] * SRC[31:0]; DEST[127:64] :=
  DEST[95:64] * SRC[95:64]` (unsigned, full 64-bit products).
* AESENC: `STATE := SRC1; RoundKey := SRC2; STATE := ShiftRows(STATE);
  STATE := SubBytes(STATE); STATE := MixColumns(STATE); DEST[127:0] :=
  STATE XOR RoundKey`.
* AESENCLAST: as AESENC, without `MixColumns`.
* AESDEC: `STATE := SRC1; RoundKey := SRC2; STATE := InvShiftRows(STATE);
  STATE := InvSubBytes(STATE); STATE := InvMixColumns(STATE); DEST[127:0] :=
  STATE XOR RoundKey`.
* AESDECLAST: as AESDEC, without `InvMixColumns`.
* AESIMC: `DEST[127:0] := InvMixColumns(SRC)`.

(`SRC1` is the destination, `SRC2` the source.) -/
def XBinOp.eval : XBinOp → BitVec 128 → BitVec 128 → BitVec 128
  | .movdqa, _, b => b
  | .paddd, a, b =>
    ofDwords (dword a 0 + dword b 0) (dword a 1 + dword b 1) (dword a 2 + dword b 2)
      (dword a 3 + dword b 3)
  | .pxor, a, b => a ^^^ b
  | .por, a, b => a ||| b
  | .punpckldq, a, b => ofDwords (dword a 0) (dword b 0) (dword a 1) (dword b 1)
  | .punpckhdq, a, b => ofDwords (dword a 2) (dword b 2) (dword a 3) (dword b 3)
  | .punpcklqdq, a, b => qword b 0 ++ qword a 0
  | .punpckhqdq, a, b => qword b 1 ++ qword a 1
  | .pshufb, a, b => ofBytes fun i =>
    let c := byte b i
    if c.msb then 0 else byte a (c.extractLsb' 0 4).toNat
  | .sha256msg1, a, b =>
    ofDwords (dword a 0 + sha256Sigma0 (dword a 1)) (dword a 1 + sha256Sigma0 (dword a 2))
      (dword a 2 + sha256Sigma0 (dword a 3)) (dword a 3 + sha256Sigma0 (dword b 0))
  | .sha256msg2, a, b => sha256Msg2 a b
  | .pand, a, b => a &&& b
  | .pandn, a, b => ~~~a &&& b
  | .paddq, a, b => (qword a 1 + qword b 1) ++ (qword a 0 + qword b 0)
  | .pmuludq, a, b =>
    ((dword a 2).setWidth 64 * (dword b 2).setWidth 64) ++
      ((dword a 0).setWidth 64 * (dword b 0).setWidth 64)
  | .aesenc, a, b => aesMixColumns (aesMapBytes aesSbox (aesShiftRows a)) ^^^ b
  | .aesenclast, a, b => aesMapBytes aesSbox (aesShiftRows a) ^^^ b
  | .aesdec, a, b => aesInvMixColumns (aesMapBytes aesInvSbox (aesInvShiftRows a)) ^^^ b
  | .aesdeclast, a, b => aesMapBytes aesInvSbox (aesInvShiftRows a) ^^^ b
  | .aesimc, _, b => aesInvMixColumns b

/-- SDM Vol. 2, the forms with an immediate count (no flags are affected):

* "PSLLW/PSLLD/PSLLQ" and "PSRLW/PSRLD/PSRLQ", doublewords: `IF (COUNT > 31)
  THEN DEST[127:0] := 0 ELSE DEST[31:0] := ZeroExtend(DEST[31:0] << COUNT)`
  (respectively `>>`, a logical shift), and likewise for doublewords 1–3.
* The same, quadwords: `IF (COUNT > 63) THEN DEST[127:0] := 0 ELSE
  DEST[63:0] := ZeroExtend(DEST[63:0] << COUNT)` (respectively `>>`), and
  likewise for quadword 1.
* "PSLLDQ" and "PSRLDQ": `TEMP := COUNT; IF (TEMP > 15) THEN TEMP := 16;
  DEST := DEST << (TEMP * 8)` (respectively `>>`, a logical shift). -/
def XShiftOp.eval (op : XShiftOp) (a : BitVec 128) (count : BitVec 8) : BitVec 128 :=
  let n := count.toNat
  let dwords (f : BitVec 32 → BitVec 32) : BitVec 128 :=
    if 31 < n then 0 else ofDwords (f (dword a 0)) (f (dword a 1)) (f (dword a 2)) (f (dword a 3))
  let qwords (f : BitVec 64 → BitVec 64) : BitVec 128 :=
    if 63 < n then 0 else f (qword a 1) ++ f (qword a 0)
  match op with
  | .pslld => dwords (· <<< n)
  | .psrld => dwords (· >>> n)
  | .psllq => qwords (· <<< n)
  | .psrlq => qwords (· >>> n)
  | .pslldq => a <<< (min n 16 * 8)
  | .psrldq => a >>> (min n 16 * 8)

/-- SDM Vol. 2, "PSHUFD": `DEST[31:0] := (SRC >> (ORDER[1:0] * 32))[31:0];
DEST[63:32] := (SRC >> (ORDER[3:2] * 32))[31:0]; DEST[95:64] := (SRC >>
(ORDER[5:4] * 32))[31:0]; DEST[127:96] := (SRC >> (ORDER[7:6] * 32))[31:0]`.
No flags are affected. -/
def shufDwords (a : BitVec 128) (order : BitVec 8) : BitVec 128 :=
  ofDwords (dword a (order.extractLsb' 0 2).toNat) (dword a (order.extractLsb' 2 2).toNat)
    (dword a (order.extractLsb' 4 2).toNat) (dword a (order.extractLsb' 6 2).toNat)

/-- SDM Vol. 2, "PALIGNR", 128-bit legacy SSE version: `temp1[255:0] :=
((DEST[127:0] << 128) OR SRC[127:0])>>(imm8*8); DEST[127:0] :=
temp1[127:0]`. No flags are affected. -/
def alignRight (dst src : BitVec 128) (imm : BitVec 8) : BitVec 128 :=
  ((dst ++ src) >>> (imm.toNat * 8)).extractLsb' 0 128

/-- SDM Vol. 2, "SHA256RNDS2", where `SRC1` is the destination, `SRC2` the
source and `wk` the implicit operand `XMM0`: `A_0 := SRC2[127:96]; B_0 :=
SRC2[95:64]; C_0 := SRC1[127:96]; D_0 := SRC1[95:64]; E_0 := SRC2[63:32];
F_0 := SRC2[31:0]; G_0 := SRC1[63:32]; H_0 := SRC1[31:0]; WK0 :=
XMM0[31:0]; WK1 := XMM0[63:32]; FOR i = 0 to 1 A_(i+1) := Ch(E_i, F_i,
G_i) + Σ1(E_i) + WKi + H_i + Maj(A_i, B_i, C_i) + Σ0(A_i); B_(i+1) := A_i;
C_(i+1) := B_i; D_(i+1) := C_i; E_(i+1) := Ch(E_i, F_i, G_i) + Σ1(E_i) +
WKi + H_i + D_i; F_(i+1) := E_i; G_(i+1) := F_i; H_(i+1) := G_i; ENDFOR
DEST[127:96] := A_2; DEST[95:64] := B_2; DEST[63:32] := E_2; DEST[31:0] :=
F_2`. No flags are affected. -/
def sha256Rnds2 (src1 src2 wk : BitVec 128) : BitVec 128 :=
  let a0 := dword src2 3
  let b0 := dword src2 2
  let c0 := dword src1 3
  let d0 := dword src1 2
  let e0 := dword src2 1
  let f0 := dword src2 0
  let g0 := dword src1 1
  let h0 := dword src1 0
  let wk0 := dword wk 0
  let wk1 := dword wk 1
  let a1 := sha256Ch e0 f0 g0 + sha256BigSigma1 e0 + wk0 + h0 + sha256Maj a0 b0 c0 +
    sha256BigSigma0 a0
  let b1 := a0
  let c1 := b0
  let d1 := c0
  let e1 := sha256Ch e0 f0 g0 + sha256BigSigma1 e0 + wk0 + h0 + d0
  let f1 := e0
  let g1 := f0
  let h1 := g0
  let a2 := sha256Ch e1 f1 g1 + sha256BigSigma1 e1 + wk1 + h1 + sha256Maj a1 b1 c1 +
    sha256BigSigma0 a1
  let b2 := a1
  let e2 := sha256Ch e1 f1 g1 + sha256BigSigma1 e1 + wk1 + h1 + d1
  let f2 := e1
  ofDwords f2 e2 b2 a2

/-- SDM Vol. 2, "AESKEYGENASSIST": `X3[31:0] := SRC[127:96]; X2[31:0] :=
SRC[95:64]; X1[31:0] := SRC[63:32]; X0[31:0] := SRC[31:0]; RCON[31:0] :=
ZeroExtend(imm8[7:0]); DEST[31:0] := SubWord(X1); DEST[63:32] :=
RotWord(SubWord(X1)) XOR RCON; DEST[95:64] := SubWord(X3); DEST[127:96] :=
RotWord(SubWord(X3)) XOR RCON`, where `SubWord` applies the S-box to each
byte and `RotWord(x) = (x >> 8) OR (x << 24)` (a 32-bit rotate right by 8).
No flags are affected. -/
def aesKeygenAssist (src : BitVec 128) (rcon : BitVec 8) : BitVec 128 :=
  let subWord (x : BitVec 32) : BitVec 32 :=
    aesSbox (x.extractLsb' 24 8) ++ aesSbox (x.extractLsb' 16 8) ++
      aesSbox (x.extractLsb' 8 8) ++ aesSbox (x.extractLsb' 0 8)
  let rc : BitVec 32 := rcon.setWidth 32
  let x1 := subWord (dword src 1)
  let x3 := subWord (dword src 3)
  ofDwords x1 (x1.rotateRight 8 ^^^ rc) x3 (x3.rotateRight 8 ^^^ rc)

/-- SDM Vol. 2, "PCLMULQDQ", 128-bit legacy SSE version: `IF (imm8[0] = 0)
THEN TEMP1 := SRC1[63:0] ELSE TEMP1 := SRC1[127:64]; IF (imm8[4] = 0) THEN
TEMP2 := SRC2[63:0] ELSE TEMP2 := SRC2[127:64]`, and `DEST[127:0]` the
carry-less product of `TEMP1` and `TEMP2` (`clmul`). No flags are affected. -/
def pclmul (src1 src2 : BitVec 128) (sel : BitVec 8) : BitVec 128 :=
  clmul (qword src1 (if sel.getLsbD 0 then 1 else 0)) (qword src2 (if sel.getLsbD 4 then 1 else 0))

/-! ### AVX

The SDM defines most VEX-encoded integer instructions on 256-bit operands as
the 128-bit operation applied to each 128-bit lane (e.g. "VPADDD (VEX.256
encoded version)": the doubleword sums of `SRC1[127:0]` and `SRC2[127:0]`
into `DEST[127:0]`, then of `SRC1[255:128]` and `SRC2[255:128]` into
`DEST[255:128]`); `VEX.128` versions compute lane 0 only and zero the rest. -/

/-- The legacy SSE instruction whose operation `op` applies to each lane:
VPADDD, VPADDQ, VPXOR, VPOR, VPAND, VPANDN, VPSHUFB, VPMULUDQ and
VPUNPCK{L,H}{DQ,QDQ} are, lane by lane, PADDD, PADDQ, PXOR, POR, PAND,
PANDN, PSHUFB, PMULUDQ and PUNPCK{L,H}{DQ,QDQ} (SDM Vol. 2, each
instruction's "VEX.256 encoded version" pseudocode, with `SRC1` in place of
the destination). -/
def VBinOp.sse : VBinOp → XBinOp
  | .vpaddd => .paddd | .vpaddq => .paddq | .vpxor => .pxor | .vpor => .por
  | .vpand => .pand | .vpandn => .pandn | .vpshufb => .pshufb | .vpmuludq => .pmuludq
  | .vpunpckldq => .punpckldq | .vpunpckhdq => .punpckhdq
  | .vpunpcklqdq => .punpcklqdq | .vpunpckhqdq => .punpckhqdq

/-- SDM Vol. 2, "VPBLENDD", for one lane (`imm` holding that lane's four
selector bits): `IF (imm8[i]) THEN DEST[32i+31:32i] := SRC2[32i+31:32i]
ELSE DEST[32i+31:32i] := SRC1[32i+31:32i]`. -/
def blendDwords (a b : BitVec 128) (imm : BitVec 4) : BitVec 128 :=
  let pick (i : Nat) : BitVec 32 := if imm.getLsbD i then dword b i else dword a i
  ofDwords (pick 0) (pick 1) (pick 2) (pick 3)

/-- SDM Vol. 2, "VPSLLVD/VPSLLVQ" and "VPSRLVD/VPSRLVQ", for one lane:
`COUNT := SRC2[32i+31:32i]; IF COUNT < 32 THEN DEST[32i+31:32i] :=
ZeroExtend(SRC1[32i+31:32i] << COUNT) ELSE DEST[32i+31:32i] := 0`
(respectively `>>`, a logical shift) for each doubleword `i`, and likewise
for quadwords with `COUNT < 64`. -/
def VVarOp.eval (op : VVarOp) (a b : BitVec 128) : BitVec 128 :=
  let dwords (f : BitVec 32 → Nat → BitVec 32) : BitVec 128 :=
    let e (i : Nat) := let n := (dword b i).toNat; if n < 32 then f (dword a i) n else 0
    ofDwords (e 0) (e 1) (e 2) (e 3)
  let qwords (f : BitVec 64 → Nat → BitVec 64) : BitVec 128 :=
    let e (i : Nat) := let n := (qword b i).toNat; if n < 64 then f (qword a i) n else 0
    e 1 ++ e 0
  match op with
  | .vpsllvd => dwords (· <<< ·)
  | .vpsrlvd => dwords (· >>> ·)
  | .vpsllvq => qwords (· <<< ·)
  | .vpsrlvq => qwords (· >>> ·)

/-- Quadword `i` (bits `64i+63:64i`) of a 256-bit value. -/
def qword256 (x : BitVec 256) (i : Nat) : BitVec 64 := x.extractLsb' (64 * i) 64

/-- SDM Vol. 2, "VPERMQ" (immediate form): `DEST[63:0] := (SRC >>
(IMM8[1:0] * 64))[63:0]; DEST[127:64] := (SRC >> (IMM8[3:2] * 64))[63:0];
DEST[191:128] := (SRC >> (IMM8[5:4] * 64))[63:0]; DEST[255:192] := (SRC >>
(IMM8[7:6] * 64))[63:0]`. -/
def permQwords (x : BitVec 256) (order : BitVec 8) : BitVec 256 :=
  let q (i : Nat) := qword256 x (order.extractLsb' (2 * i) 2).toNat
  q 3 ++ q 2 ++ q 1 ++ q 0

/-- SDM Vol. 2, "VPERM2I128": `CASE IMM8[1:0] of 0: DEST[127:0] :=
SRC1[127:0]; 1: DEST[127:0] := SRC1[255:128]; 2: DEST[127:0] :=
SRC2[127:0]; 3: DEST[127:0] := SRC2[255:128]`, likewise `IMM8[5:4]` for
`DEST[255:128]`; `IF (imm8[3]) DEST[127:0] := 0; IF (imm8[7])
DEST[255:128] := 0`. Here `a i` and `b i` are lane `i` of `SRC1` and
`SRC2`, and the result is lane `j` of `DEST`. -/
def perm2Lanes (a b : Nat → BitVec 128) (sel : BitVec 8) (j : Nat) : BitVec 128 :=
  if sel.getLsbD (4 * j + 3) then 0 else
    let k := (sel.extractLsb' (4 * j) 2).toNat
    if k < 2 then a (k % 2) else b (k % 2)

/-- Semantics of an AVX instruction that writes only vector registers. SDM
Vol. 2 (no flags are affected; `VEX.128` versions zero `DEST[MAXVL-1:128]`):

* The lane-wise instructions: see `VBinOp.sse`, `XShiftOp.eval` (VPSLLD,
  VPSRLD, VPSLLQ, VPSRLQ, VPSLLDQ and VPSRLDQ with an immediate count, each
  lane as the legacy SSE form on `SRC`), `shufDwords` (VPSHUFD, each lane
  with the same `imm8`), `alignRight` (VPALIGNR: `temp1[255:0] :=
  ((SRC1[127:0] << 128) OR SRC2[127:0]) >> (imm8*8)`, and likewise for
  bits 255:128), `blendDwords` (VPBLENDD, lane `j` selected by
  `imm8[4j+3:4j]`), and `VVarOp.eval`.
* VMOVDQA (register form): `DEST[255:0] := SRC[255:0]` (`VEX.128`:
  `DEST[127:0] := SRC[127:0]`).
* VPBROADCASTD/VPBROADCASTQ (register source): every doubleword
  (quadword) of `DEST` is `SRC[31:0]` (`SRC[63:0]`).
* VPERMQ: see `permQwords`. VPERM2I128: see `perm2Lanes`.
* VINSERTI128: `TEMP[255:0] := SRC1[255:0]; CASE (imm8[0]) OF 0:
  TEMP[127:0] := SRC2[127:0]; 1: TEMP[255:128] := SRC2[127:0]; DEST :=
  TEMP`.
* VEXTRACTI128 (register destination): `CASE (imm8[0]) OF 0: DEST[127:0]
  := SRC1[127:0]; 1: DEST[127:0] := SRC1[255:128]; DEST[MAXVL-1:128] := 0`.
* VMOVQ xmm, r64: `DEST[63:0] := SRC[63:0]; DEST[MAXVL-1:64] := 0`.
* VZEROUPPER: in 64-bit mode, `YMM0[MAXVL-1:128] := 0` … `YMM15[MAXVL-1:128]
  := 0`. -/
def VOp.exec : VOp → State → State
  | .vbin op len d a b, s =>
    s.setV len d (op.sse.eval (s.lane a 0) (s.lane b 0)) (op.sse.eval (s.lane a 1) (s.lane b 1))
  | .vmovdqa len d r, s => s.setV len d (s.lane r 0) (s.lane r 1)
  | .vshift op len d r n, s => s.setV len d (op.eval (s.lane r 0) n) (op.eval (s.lane r 1) n)
  | .vpshufd len d r o, s => s.setV len d (shufDwords (s.lane r 0) o) (shufDwords (s.lane r 1) o)
  | .vpalignr len d a b n, s =>
    s.setV len d (alignRight (s.lane a 0) (s.lane b 0) n) (alignRight (s.lane a 1) (s.lane b 1) n)
  | .vpblendd len d a b n, s =>
    s.setV len d (blendDwords (s.lane a 0) (s.lane b 0) (n.extractLsb' 0 4))
      (blendDwords (s.lane a 1) (s.lane b 1) (n.extractLsb' 4 4))
  | .vvar op len d a b, s =>
    s.setV len d (op.eval (s.lane a 0) (s.lane b 0)) (op.eval (s.lane a 1) (s.lane b 1))
  | .vpbroadcastd len d r, s =>
    let v := dword (s.xmm r) 0
    let x := ofDwords v v v v
    s.setV len d x x
  | .vpbroadcastq len d r, s =>
    let x := qword (s.xmm r) 0 ++ qword (s.xmm r) 0
    s.setV len d x x
  | .vpermq d r o, s =>
    let x := permQwords (s.ymm r) o
    s.setV .l256 d (x.extractLsb' 0 128) (x.extractLsb' 128 128)
  | .vperm2i128 d a b n, s =>
    s.setV .l256 d (perm2Lanes (s.lane a) (s.lane b) n 0) (perm2Lanes (s.lane a) (s.lane b) n 1)
  | .vinserti128 d a b n, s =>
    if n.getLsbD 0 then s.setV .l256 d (s.lane a 0) (s.xmm b)
    else s.setV .l256 d (s.xmm b) (s.lane a 1)
  | .vextracti128 d r n, s => s.setV .l128 d (s.lane r (if n.getLsbD 0 then 1 else 0)) 0
  | .vmovq d r, s => s.setV .l128 d ((0 : BitVec 64) ++ s.gpr r) 0
  | .vzeroupper, s => { s with ymmHi := fun _ => 0 }

/-- Semantics of an SSE instruction that writes only an SSE register. MOVQ
with an XMM destination: SDM Vol. 2, "MOVD/MOVQ", 128-bit legacy SSE
version: `DEST[63:0] := SRC[63:0]; DEST[127:64] := 0000000000000000H`. No
flags are affected. -/
def XOp.exec : XOp → State → State
  | .bin op d r, s => s.setXmm d (op.eval (s.xmm d) (s.xmm r))
  | .shift op d n, s => s.setXmm d (op.eval (s.xmm d) n)
  | .pshufd d r o, s => s.setXmm d (shufDwords (s.xmm r) o)
  | .palignr d r n, s => s.setXmm d (alignRight (s.xmm d) (s.xmm r) n)
  | .sha256rnds2 d r, s => s.setXmm d (sha256Rnds2 (s.xmm d) (s.xmm r) (s.xmm .xmm0))
  | .movq d r, s => s.setXmm d ((0 : BitVec 64) ++ s.gpr r)
  | .aeskeygenassist d r n, s => s.setXmm d (aesKeygenAssist (s.xmm r) n)
  | .pclmulqdq d r n, s => s.setXmm d (pclmul (s.xmm d) (s.xmm r) n)

/-- The CPU features an instruction needs beyond the x86-64 baseline
(x86-64-v1, which includes SSE and SSE2: System V AMD64 psABI,
"Micro-Architecture Levels"), named as Rust's target features. SDM Vol. 2,
the "CPUID Feature Flag" column of each instruction's opcode table: SSSE3
for PSHUFB and PALIGNR (`66 0F 38 00 /r`, `66 0F 3A 0F /r ib`), SHA for
SHA256RNDS2, SHA256MSG1 and SHA256MSG2 (`NP 0F 38 CB /r`, `NP 0F 38 CC /r`,
`NP 0F 38 CD /r`); AES for AESENC, AESENCLAST, AESDEC, AESDECLAST, AESIMC
and AESKEYGENASSIST (`66 0F 38 DC /r`, `66 0F 38 DD /r`, `66 0F 38 DE /r`,
`66 0F 38 DF /r`, `66 0F 38 DB /r`, `66 0F 3A DF /r ib`); PCLMULQDQ for
PCLMULQDQ (`66 0F 3A 44 /r ib`); SSE2 for MOVQ xmm, r64 (`66 REX.W 0F 6E /r`),
PAND, PANDN, PADDQ, PMULUDQ, PSLLQ, PSRLQ, PSLLDQ and PSRLDQ; AVX for the
VEX.128 forms of the lane-wise instructions (e.g. `VEX.128.66.0F.WIG FE /r`
VPADDD), for VMOVDQA, VMOVDQU (both lengths), VMOVQ and VZEROUPPER; AVX2 for
their VEX.256 forms (e.g. `VEX.256.66.0F.WIG FE /r` VPADDD) and for VPBLENDD,
VPSLLVD/Q, VPSRLVD/Q, VPBROADCASTD/Q, VPERMQ, VPERM2I128, VINSERTI128,
VEXTRACTI128 and VBROADCASTI128 at any length. LDMXCSR and STMXCSR (SSE,
`NP 0F AE /2`, `NP 0F AE /3`) and LFENCE (SSE2, `NP 0F AE E8`) are in the
baseline. -/
def Instr.requires : Instr → List String
  | .xop (.bin .pshufb ..) | .xop (.palignr ..) => ["ssse3"]
  | .xop (.bin .sha256msg1 ..) | .xop (.bin .sha256msg2 ..) | .xop (.sha256rnds2 ..) => ["sha"]
  | .xop (.bin .aesenc ..) | .xop (.bin .aesenclast ..) | .xop (.bin .aesdec ..)
  | .xop (.bin .aesdeclast ..) | .xop (.bin .aesimc ..) | .xop (.aeskeygenassist ..) => ["aes"]
  | .xop (.pclmulqdq ..) => ["pclmulqdq"]
  | .vop (.vbin _ .l256 ..) | .vop (.vshift _ .l256 ..) | .vop (.vpshufd .l256 ..)
  | .vop (.vpalignr .l256 ..) => ["avx2"]
  | .vop (.vbin _ .l128 ..) | .vop (.vshift _ .l128 ..) | .vop (.vpshufd .l128 ..)
  | .vop (.vpalignr .l128 ..) | .vop (.vmovdqa ..) | .vop (.vmovq ..) | .vop .vzeroupper
  | .vmovdquLoad .. | .vmovdquStore .. => ["avx"]
  | .vop (.vpblendd ..) | .vop (.vvar ..) | .vop (.vpbroadcastd ..) | .vop (.vpbroadcastq ..)
  | .vop (.vpermq ..) | .vop (.vperm2i128 ..) | .vop (.vinserti128 ..) | .vop (.vextracti128 ..)
  | .vbroadcasti128 .. => ["avx2"]
  | _ => []

/-- Semantics of an instruction. The byte forms: SDM Vol. 2, "MOVZX":
`DEST := ZeroExtend(SRC)` (with a 32-bit destination, zero-extended to 64
bits, SDM Vol. 1 §3.4.1.1), and "MOV": `DEST := SRC`, where the source of a
byte store is the register's low byte (AL, CL, DL, BL, SPL, BPL, SIL, DIL,
R8B–R15B; SDM Vol. 1 §3.4.1.1). Neither affects the flags. -/
def exec : Instr → State → Option State
  | .mov d src, s => (readSrc s src).map fun v => s.setReg d v
  | .store m r, s => s.store64 (s.ea m) (s.gpr r)
  | .alu op d src, s => execAlu op d src s
  | .mov32 d src, s => (readSrc32 s src).map fun v => s.setReg32 d v
  | .store32 m r, s => s.store32 (s.ea m) ((s.gpr r).setWidth 32)
  | .alu32 op d src, s => execAlu32 op d src s
  | .shift32 op d n, s => execShift32 op d n s
  | .bswap32 d, s => some (s.setReg32 d (bswap32 ((s.gpr d).setWidth 32)))
  | .movzx8 d m, s => (s.load8 (s.ea m)).map fun v => s.setReg d (v.setWidth 64)
  | .store8 m r, s => s.store8 (s.ea m) ((s.gpr r).setWidth 8)
  | .bswap d, s => some (s.setReg d (bswap64 (s.gpr d)))
  | .shift op d n, s => execShift op d n s
  -- SDM Vol. 2, "MOV": `DEST := SRC`; no flags are affected.
  | .movImm64 d v, s => some (s.setReg d v)
  -- SDM Vol. 2, "MOVDQU": `DEST[127:0] := SRC[127:0]`, with memory in
  -- little-endian byte order (SDM Vol. 1 §1.3.1); no alignment is required
  -- and no flags are affected.
  | .movdquLoad d m, s => (s.load128 (s.ea m)).map fun v => s.setXmm d v
  | .movdquStore m r, s => s.store128 (s.ea m) (s.xmm r)
  | .xop op, s => some (op.exec s)
  | .vop op, s => some (op.exec s)
  -- SDM Vol. 2, "MOVDQU" (VEX.128 and VEX.256 versions): `DEST[127:0] :=
  -- SRC[127:0]; DEST[MAXVL-1:128] := 0`, respectively `DEST[255:0] :=
  -- SRC[255:0]`, and for a store the 16 or 32 bytes of the source; no
  -- alignment is required.
  | .vmovdquLoad .l128 d m, s => (s.load128 (s.ea m)).map fun v => s.setV .l128 d v 0
  | .vmovdquLoad .l256 d m, s =>
    (s.load256 (s.ea m)).map fun v => s.setV .l256 d (v.extractLsb' 0 128) (v.extractLsb' 128 128)
  | .vmovdquStore .l128 m r, s => s.store128 (s.ea m) (s.xmm r)
  | .vmovdquStore .l256 m r, s => s.store256 (s.ea m) (s.ymm r)
  -- SDM Vol. 2, "VBROADCAST": `DEST[127:0] := SRC[127:0]; DEST[255:128] :=
  -- SRC[127:0]`; no alignment is required.
  | .vbroadcasti128 d m, s => (s.load128 (s.ea m)).map fun v => s.setV .l256 d v v
  -- SDM Vol. 2, "STMXCSR": `m32 := MXCSR`. "LDMXCSR": `MXCSR := m32`, with
  -- #GP(0) "for an attempt to set reserved bits in MXCSR", which are bits
  -- 31:16 (SDM Vol. 1 §10.2.3); on processors without DAZ, bit 6 is
  -- reserved too (§11.6.6, `MXCSR_MASK`), which the model does not know: it
  -- is loaded only with values without it, or saved from MXCSR itself.
  -- "LFENCE": it orders instructions and has no architectural effect.
  -- None of them affects the flags.
  | .stmxcsr m, s => s.store32 (s.ea m) s.mxcsr
  | .ldmxcsr m, s => (s.load32 (s.ea m)).bind fun v =>
    if v.extractLsb' 16 16 = 0 then some { s with mxcsr := v } else none
  | .lfence, s => some s

def addrs : Instr → State → List Addr
  | .mov _ src, s => srcAddrs s src
  | .store m _, s => [s.ea m]
  | .alu _ _ src, s => srcAddrs s src
  | .mov32 _ src, s => srcAddrs s src
  | .store32 m _, s => [s.ea m]
  | .alu32 _ _ src, s => srcAddrs s src
  | .shift32 .., _ => []
  | .bswap32 _, _ => []
  | .movzx8 _ m, s => [s.ea m]
  | .store8 m _, s => [s.ea m]
  | .bswap _, _ => []
  | .shift .., _ => []
  | .movImm64 .., _ => []
  | .movdquLoad _ m, s => [s.ea m]
  | .movdquStore m _, s => [s.ea m]
  | .xop _, _ => []
  | .vop _, _ => []
  | .vmovdquLoad _ _ m, s => [s.ea m]
  | .vmovdquStore _ m _, s => [s.ea m]
  | .vbroadcasti128 _ m, s => [s.ea m]
  | .stmxcsr m, s => [s.ea m]
  | .ldmxcsr m, s => [s.ea m]
  | .lfence, _ => []

def eval : Cond → State → Option Bool
  | .e, s => s.zf
  | .ne, s => s.zf.map (!·)
  | .b, s => s.cf
  | .ae, s => s.cf.map (!·)

/-- SDM Vol. 2, "CALL", near call: `RSP := RSP − 8; Memory[RSP] := RIP`
(`Push(RIP)`, where `RIP` is the address of the next instruction), then the
jump. No flags are affected. The return address is the next of the state's. -/
def call (s : State) : Option State :=
  let sp := s.gpr .rsp - 8
  some { s.setReg .rsp sp with
    mem := s.mem.writeW sp (s.unknowns 0)
    unknowns := fun n => s.unknowns (n + 1) }

/-- SDM Vol. 2, "RET", near return: `RIP := Pop()`, i.e. `RIP :=
Memory[RSP]; RSP := RSP + 8`. No flags are affected. It returns after the
call instruction if `RSP` and the return address at `[RSP]` are those the
call left (`s₁`); otherwise the model faults. -/
def ret (s₁ s₂ : State) : Option State :=
  if s₂.gpr .rsp = s₁.gpr .rsp ∧ s₂.mem.readW (s₂.gpr .rsp) 64 = s₁.mem.readW (s₁.gpr .rsp) 64 then
    some (s₂.setReg .rsp (s₂.gpr .rsp + 8))
  else none

/-- The register an instruction writes, if any. -/
def Instr.dst : Instr → Option Reg
  | .mov d _ | .alu _ d _ | .mov32 d _ | .alu32 _ d _ | .shift32 _ d _ | .bswap32 d
  | .movzx8 d _ | .bswap d | .shift _ d _ | .movImm64 d _ => some d
  | .store .. | .store32 .. | .store8 .. | .movdquLoad .. | .movdquStore .. | .xop _
  | .vop _ | .vmovdquLoad .. | .vmovdquStore .. | .vbroadcasti128 .. | .stmxcsr _ | .ldmxcsr _
  | .lfence => none

abbrev isa : ISA where
  State := State
  Instr := Instr
  Cond := Cond
  exec := exec
  addrs := addrs
  eval := eval
  call := call
  callAddrs s := [s.gpr .rsp - 8]
  ret := ret
  retAddrs s := [s.gpr .rsp]
  writesSp i := i.dst == some .rsp
  -- No frames are modelled.
  push _ _ := none
  pop _ _ _ := none
  requires := Instr.requires

end VG.X86_64
