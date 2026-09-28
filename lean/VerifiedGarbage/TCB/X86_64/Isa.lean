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
  §10.2.2); the upper bits of the `ymm`/`zmm` registers they alias are not
  modelled, and the legacy SSE instructions modelled here leave them
  unmodified. Every SSE instruction is register-to-register, except the
  unaligned `movdqu` load and store, so no alignment fault (legacy SSE
  memory operands must be 16-byte aligned) needs modelling. MXCSR is not
  modelled: no modelled SSE instruction reads or writes it (integer SSE
  instructions raise no SIMD floating-point exceptions).
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

/-- Two-operand SSE2 instructions `op xmm1, xmm2` (register forms only). -/
inductive XBinOp
  | movdqa | paddd | pxor | por | punpckldq | punpckhdq | punpcklqdq | punpckhqdq
  deriving DecidableEq, Repr

/-- SSE2 shifts of each doubleword by an immediate count. -/
inductive XShiftOp | pslld | psrld
  deriving DecidableEq, Repr

/-- SSE2 instructions that only read and write SSE registers. -/
inductive XOp
  /-- `op xmm1, xmm2` -/
  | bin (op : XBinOp) (dst src : XReg)
  /-- `op xmm1, imm8` -/
  | shift (op : XShiftOp) (dst : XReg) (count : BitVec 8)
  /-- `pshufd xmm1, xmm2, imm8` -/
  | pshufd (dst src : XReg) (order : BitVec 8)
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
  /-- An SSE2 instruction on SSE registers only. -/
  | xop (op : XOp)
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

/-! ### SSE2

The SDM's pseudocode numbers bits from the least significant: doubleword `i`
of a 128-bit operand is bits `32i+31:32i`, quadword `i` bits `64i+63:64i`. -/

/-- Doubleword `i` of `x`: bits `32i+31:32i`. -/
def dword (x : BitVec 128) (i : Nat) : BitVec 32 := x.extractLsb' (32 * i) 32

/-- Quadword `i` of `x`: bits `64i+63:64i`. -/
def qword (x : BitVec 128) (i : Nat) : BitVec 64 := x.extractLsb' (64 * i) 64

/-- The 128-bit value with doublewords `d0` (bits 31:0), `d1`, `d2`, `d3` (bits 127:96). -/
def ofDwords (d0 d1 d2 d3 : BitVec 32) : BitVec 128 := d3 ++ d2 ++ d1 ++ d0

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

/-- SDM Vol. 2, "PSLLW/PSLLD/PSLLQ" and "PSRLW/PSRLD/PSRLQ", the doubleword
forms with an immediate count: `IF (COUNT > 31) THEN DEST[127:0] := 0 ELSE
DEST[31:0] := ZeroExtend(DEST[31:0] << COUNT)` (respectively `>>`, a logical
shift), and likewise for doublewords 1–3. No flags are affected. -/
def XShiftOp.eval (op : XShiftOp) (a : BitVec 128) (count : BitVec 8) : BitVec 128 :=
  let n := count.toNat
  if 31 < n then 0 else
    let f : BitVec 32 → BitVec 32 := match op with
      | .pslld => (· <<< n)
      | .psrld => (· >>> n)
    ofDwords (f (dword a 0)) (f (dword a 1)) (f (dword a 2)) (f (dword a 3))

/-- SDM Vol. 2, "PSHUFD": `DEST[31:0] := (SRC >> (ORDER[1:0] * 32))[31:0];
DEST[63:32] := (SRC >> (ORDER[3:2] * 32))[31:0]; DEST[95:64] := (SRC >>
(ORDER[5:4] * 32))[31:0]; DEST[127:96] := (SRC >> (ORDER[7:6] * 32))[31:0]`.
No flags are affected. -/
def shufDwords (a : BitVec 128) (order : BitVec 8) : BitVec 128 :=
  ofDwords (dword a (order.extractLsb' 0 2).toNat) (dword a (order.extractLsb' 2 2).toNat)
    (dword a (order.extractLsb' 4 2).toNat) (dword a (order.extractLsb' 6 2).toNat)

/-- Semantics of an SSE2 instruction on SSE registers only. -/
def XOp.exec : XOp → State → State
  | .bin op d r, s => s.setXmm d (op.eval (s.xmm d) (s.xmm r))
  | .shift op d n, s => s.setXmm d (op.eval (s.xmm d) n)
  | .pshufd d r o, s => s.setXmm d (shufDwords (s.xmm r) o)

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
  | .store .. | .store32 .. | .store8 .. | .movdquLoad .. | .movdquStore .. | .xop _ => none

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
  -- Every modelled instruction is in the x86-64 baseline (x86-64-v1), which
  -- includes SSE and SSE2 (System V AMD64 psABI, "Micro-Architecture Levels").
  requires _ := []

end VG.X86_64
