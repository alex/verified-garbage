import VerifiedGarbage.TCB.X86_64.State

/-!
# x86-64 general-purpose instructions

**Trusted.** The semantics of the general-purpose (integer) instructions of
the x86-64 model in `TCB/X86_64/Isa.lean`: source operands, the ALU
operations and their flags, shifts, rotates (including BMI2's `rorx`), BMI1's
`andn`, byte swaps and `mul`.
-/

namespace VG.X86_64

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

/-- SDM Vol. 2, "RORX—Rotate Right Logical Without Affecting Flags", for a
32-bit operand: `y := imm8 AND 1FH; DEST := (SRC >> y) | (SRC << (32 - y))`,
zero-extended (SDM Vol. 1 §3.4.1.1); "This instruction does not update any
flags." Only counts `1 ≤ n ≤ 31` are modelled (so the masked count is `n`);
other counts fault. -/
def execRorx32 (dst src : Reg) (n : Nat) (s : State) : Option State :=
  if 1 ≤ n ∧ n ≤ 31 then some (s.setReg32 dst (((s.gpr src).setWidth 32).rotateRight n))
  else none

/-- SDM Vol. 2, "ANDN—Logical AND NOT", for 32-bit operands: `DEST := (NOT
SRC1) bitwiseAND SRC2`, zero-extended (SDM Vol. 1 §3.4.1.1); "SF and ZF
flags are updated based on result. OF and CF flags are cleared. AF and PF
flags are undefined." (AF and PF are not modelled.) -/
def execAndn32 (dst src1 src2 : Reg) (s : State) : State :=
  let r := ~~~((s.gpr src1).setWidth 32) &&& (s.gpr src2).setWidth 32
  (arithFlags s r false false).setReg32 dst r

/-- SDM Vol. 2, "RORX—Rotate Right Logical Without Affecting Flags", for a
64-bit operand: `y := imm8 AND 3FH; DEST := (SRC >> y) | (SRC << (64 - y))`;
"This instruction does not update any flags." Only counts `1 ≤ n ≤ 63` are
modelled (so the masked count is `n`); other counts fault. -/
def execRorx (dst src : Reg) (n : Nat) (s : State) : Option State :=
  if 1 ≤ n ∧ n ≤ 63 then some (s.setReg dst ((s.gpr src).rotateRight n)) else none

/-- SDM Vol. 2, "ANDN—Logical AND NOT", for 64-bit operands: `DEST := (NOT
SRC1) bitwiseAND SRC2`; "SF and ZF flags are updated based on result. OF and
CF flags are cleared. AF and PF flags are undefined." (AF and PF are not
modelled.) -/
def execAndn (dst src1 src2 : Reg) (s : State) : State :=
  let r := ~~~(s.gpr src1) &&& s.gpr src2
  (arithFlags s r false false).setReg dst r

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

/-- SDM Vol. 2, "MUL—Unsigned Multiply", for a 64-bit operand: `RDX:RAX :=
RAX ∗ SRC` (the 128-bit product of the unsigned operands, its high half in
RDX and its low half in RAX). "The OF and CF flags are set to 0 if the upper
half of the result is 0; otherwise, they are set to 1. The SF, ZF, AF, and PF
flags are undefined." (AF and PF are not modelled.) -/
def execMul (src : Reg) (s : State) : State :=
  let p := (s.gpr .rax).toNat * (s.gpr src).toNat
  let hi : BitVec 64 := BitVec.ofNat 64 (p / 2 ^ 64)
  ((s.setFlags (some (hi != 0)) (some (hi != 0)) none none).setReg .rax (BitVec.ofNat 64 p)).setReg
    .rdx hi

end VG.X86_64
