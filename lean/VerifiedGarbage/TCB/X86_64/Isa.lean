import VerifiedGarbage.TCB.Code
import VerifiedGarbage.TCB.X86_64.Gpr
import VerifiedGarbage.TCB.X86_64.Avx

/-!
# x86-64 machine model

**Trusted.** A model of the subset of x86-64 used by our implementations.
Each instruction's semantics here must agree with the Intel SDM; when adding
an instruction, cite the SDM pseudocode it transcribes.

The model is split by instruction family: `State.lean` holds the registers,
the state and memory operands; `Gpr.lean`, `Sse.lean` and `Avx.lean` the
semantics of the general-purpose, SSE and AVX instructions; and this file the
instructions themselves, the CPU features they require, and `exec`, which
dispatches to those semantics.

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
  be added: the constant-time leakage model assumes they do not exist. `mul`
  is one of the instructions whose timing Intel documents as independent of
  their data operands ("Data Operand Independent Timing Instruction Set
  Architecture (ISA) Guidance", which lists `MUL`).
* Calls (`call`) and returns (`ret`) are near and direct (SDM Vol. 2, "CALL",
  "RET"). The return addresses are the next of the state's `unknowns`,
  which nothing constrains (see `TCB/Code.lean`).
* `push` and `pop` (of 64-bit registers other than `rsp`) only occur as the
  push and pop of a frame (see `push`), as a sequence of them. A caller
  passes arguments on the stack by pushing them, the last first, just
  before the call: on the callee's entry the first is then at `[rsp + 8]`,
  above the return address.
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
  /-- `mul r64` (REX.W + F7 /4): the unsigned product `RDX:RAX := RAX * r64`. -/
  | mul (src : Reg)
  /-- `push r64` (50+rd) for each `r` of `rs`, in order: the push of a frame
  (see `push`); `rs` must not be empty or contain `rsp` -/
  | push (rs : List Reg)
  /-- `pop r64` (58+rd), `k` times: the pop of a frame of `8 * k` bytes (see
  `pop`); `k > 0`, and `r` is not `rsp` -/
  | pop (r : Reg) (k : Nat)
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
  | .mul r, s => some (execMul r s)
  -- Only the push and pop of a frame (`push`, `pop`).
  | .push _, _ | .pop .., _ => none

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
  | .mul _, _ => []
  | .push rs, s => (List.range rs.length).map fun i => s.gpr .rsp - BitVec.ofNat 64 (8 * (i + 1))
  | .pop _ k, s => (List.range k).map fun i => s.gpr .rsp + BitVec.ofNat 64 (8 * i)

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

/-- `push r` for each of `rs`, in order, where `r ≠ rsp`: SDM Vol. 2,
"PUSH—Push Word, Doubleword, or Quadword Onto the Stack", with a 64-bit
stack address size and operand size (the default for `PUSH r64` in 64-bit
mode): `RSP := RSP − 8; Memory[SS:RSP] := SRC; (* push quadword *)`. No
flags are affected. -/
def pushRegs (s : State) : List Reg → State
  | [] => s
  | r :: rs =>
    let sp := s.gpr .rsp - 8
    pushRegs { s.setReg .rsp sp with mem := s.mem.writeW sp (s.gpr r) } rs

/-- `pop r`, `k` times, where `r ≠ rsp`: SDM Vol. 2, "POP—Pop a Value From
the Stack", with a 64-bit stack address size and operand size (the default
for `POP r64` in 64-bit mode): `DEST := Memory[SS:RSP]; (* Copy quadword *)
RSP := RSP + 8;`. No flags are affected. -/
def popReg (s : State) (r : Reg) : Nat → State
  | 0 => s
  | k + 1 =>
    popReg ((s.setReg r (s.mem.readW (s.gpr .rsp) 64)).setReg .rsp (s.gpr .rsp + 8)) r k

/-- The push of a frame: `push r` for each `r` of `rs` (`pushRegs`). The
`8 * rs.length` bytes it stores become a writable region, at the head of
`wr`. Faults if `rs` is empty or contains `rsp`, or if the frame would wrap
around the address space. -/
def push : Instr → State → Option State
  | .push rs, s =>
    let n := 8 * rs.length
    if rs ≠ [] ∧ .rsp ∉ rs ∧ n ≤ (s.gpr .rsp).toNat then
      some { pushRegs s rs with wr := ⟨s.gpr .rsp - BitVec.ofNat 64 n, n⟩ :: s.wr }
    else none
  | _, _ => none

/-- The pop of a frame: `pop r`, `k` times (`popReg`), so that `r` holds the
last quadword of the frame. Faults if `k = 0` or `r` is `rsp`, and unless
`rsp` and the writable regions are those the push left (`s₁`), and the
frame, the region at their head, has `8 * k` bytes; it removes the frame. -/
def pop : Instr → State → State → Option State
  | .pop r k, s₁, s₂ =>
    if k ≠ 0 ∧ r ≠ .rsp ∧ s₂.gpr .rsp = s₁.gpr .rsp ∧ s₂.wr = s₁.wr ∧
        s₁.wr.head? = some ⟨s₁.gpr .rsp, 8 * k⟩ then
      some { popReg s₂ r k with wr := s₂.wr.tail }
    else none
  | _, _, _ => none

/-- The general-purpose register an instruction writes, if it writes exactly
one (the pop of a frame also moves `rsp`, as the push does): `mul` writes
two, `rax` and `rdx`, and stores and SSE instructions none. -/
def Instr.dst : Instr → Option Reg
  | .mov d _ | .alu _ d _ | .mov32 d _ | .alu32 _ d _ | .shift32 _ d _ | .bswap32 d
  | .movzx8 d _ | .bswap d | .shift _ d _ | .movImm64 d _ | .pop d _ => some d
  | .store .. | .store32 .. | .store8 .. | .movdquLoad .. | .movdquStore .. | .xop _
  | .vop _ | .vmovdquLoad .. | .vmovdquStore .. | .vbroadcasti128 .. | .stmxcsr _ | .ldmxcsr _
  | .lfence | .mul _ | .push _ => none

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
  -- Other than as the push and pop of a frame. `mul` writes `rax` and
  -- `rdx`, never `rsp`.
  writesSp i := i.dst == some .rsp
  push := push
  pop := pop
  requires := Instr.requires

end VG.X86_64
