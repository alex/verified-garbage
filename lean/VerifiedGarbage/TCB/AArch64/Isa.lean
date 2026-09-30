import VerifiedGarbage.TCB.Code
import VerifiedGarbage.TCB.AArch64.Simd

/-!
# AArch64 machine model

**Trusted.** A model of the subset of AArch64 (A64) used by our
implementations. Each instruction's semantics here must agree with the Arm
Architecture Reference Manual for A-profile (DDI 0487), chapter C6 ("A64
Base Instruction Descriptions") and, for the AdvSIMD and cryptographic
instructions, chapter C7 ("A64 Advanced SIMD and Floating-point Instruction
Descriptions"); when adding an instruction, cite the section whose
pseudocode it transcribes.

Modelling choices:
* Registers are `x0`–`x17`, `x19`–`x28` and `x30`. `x18` is not modelled, so no
  code can use it: it is the platform register (AAPCS64 §6.1.1, "r18 …
  The Platform Register, if needed; otherwise a temporary register", and
  "software developers creating platform-independent code are advised to
  avoid using r18 if at all possible"). Apple's platforms reserve it ("The
  platform reserves register x18. Don't use this register.", *Writing ARM64
  code for Apple platforms*) and Windows points it at the thread's TEB
  (*Overview of ARM64 ABI conventions*), so it may change under a function
  that writes it, and restoring it before returning is not enough.
* `x29` is not modelled either: the portable target keeps the inherited
  frame pointer intact throughout execution. AAPCS64 section 6.4.6 delegates
  frame-chain requirements to the platform; Apple requires `x29` to always
  address a valid frame record, even when a leaf function omits its own
  record (*Writing ARM64 code for Apple platforms*, "Respect the purpose of
  specific CPU registers"). Saving and restoring an arbitrary temporary in
  `x29` would not satisfy that requirement.
  https://developer.apple.com/documentation/xcode/writing-arm64-code-for-apple-platforms
* The stack pointer is separate. Only the push and pop of a frame
  (`str`/`ldr` with writeback, see `push`) write it, and only they and
  `ldrSp` (a 64-bit load from `[sp, #off]`, which reads the arguments a
  caller passed on the stack) read it; register number 31, SP or the zero
  register, is otherwise never an operand.
  Each operand is a 32-bit (`w`) or a 64-bit (`x`) register; a 32-bit
  result is zero-extended into the 64-bit register (DDI 0487, the pseudocode
  accessor `X[n, width] = value` sets `_R[n] = ZeroExtend(value, 64)`).
* Of the condition flags, only PSTATE.C is observable: ADDS/ADCS/SUBS/SBCS
  write it and ADCS/SBCS read it. N, Z and V are not observable by any
  modelled instruction; control flow uses `cbz`/`cbnz`. A call makes C
  unknown, since NZCV is undefined at a public interface (AAPCS64 §6.1.1).
* Immediates that the instruction cannot encode make the instruction fault,
  so verified code only ever contains encodable instructions.
* Memory accesses (32-bit, 64-bit, and single bytes via `ldrb`/`strb`) must
  lie within the state's permitted regions: loads within `rd ++ wr`, stores
  within `wr`; otherwise the instruction faults. Memory is little-endian.
* Instructions whose timing depends on their operands (e.g. `udiv`) must never
  be added: the constant-time leakage model assumes they do not exist. The
  multiplies (`madd`, `mul`) and the shifts (`lsl`, `lsr`: UBFM) are among the
  data-processing instructions that Arm specifies to take a time independent
  of their data when PSTATE.DIT is 1 (DDI 0487, "About PSTATE.DIT", FEAT_DIT,
  which lists MADD and UBFM, as it does the other modelled data-processing
  instructions that read a register: ADD, SUB, AND, EOR, ORR, EXTR, REV and
  MOVK, ADDS, ADCS, SUBS, SBCS and UMULH). The code does not set PSTATE.DIT,
  for these as for the others.
* Calls are `bl` and returns `ret` (DDI 0487, C6.2 "BL", "RET"). The return
  addresses are the next of the state's `unknowns`, which nothing constrains
  (see `TCB/Code.lean`). A linker veneer between a `bl` and its target may
  change `x16` and `x17` (IP0, IP1: AAPCS64 §6.1.1, "Use of IP0 and IP1 by
  the linker"), so a call leaves unknown values in them too.
* The stack pointer is always 16-byte aligned (AAPCS64 §6.4.5.1, "SP mod 16
  = 0"), and a frame moves it by 16 bytes, so the model does not check the
  stack alignment that the push and pop of a frame require.
* The SIMD and floating-point registers are `v0`–`v7` and `v16`–`v31`, 128
  bits each (DDI 0487 B1.2.1). `v8`–`v15` are not modelled, so no code can
  use them: the low 64 bits of each are callee-saved (AAPCS64 §6.1.2), and
  leaving them out keeps `abiPreserved` true of all code. A write of a
  scalar (`S`) register sets the other bits of its vector register to zero
  (the pseudocode accessor `V[n, width] = value` sets `_Z[n] =
  ZeroExtend(value, MAX_VL)`), and the modelled vector forms all write 128
  bits, so no upper bits beyond 128 (SVE's `Z` registers) are observable to
  the model; with SVE, those are also zeroed.
* No modelled AdvSIMD instruction is a floating-point one, and the one
  saturating instruction, SQDMULH, faults in the model where it would
  saturate (and set FPSR.QC), so verified code never saturates: no modelled
  instruction reads FPCR or writes FPSR, and neither is modelled. The loads and
  stores of a vector register (`LDR`/`STR (immediate, SIMD&FP)`) need no
  alignment: they access Normal memory, and alignment is checked only if
  `SCTLR_ELx.A` is 1 (DDI 0487 B2.5.2, "Alignment of data accesses"), which
  Linux, macOS and Windows leave 0 for user code.
* The AdvSIMD data-processing instructions modelled here (MOV = ORR, MOVI,
  DUP, INS, UMOV, AND, ORR, EOR, BIC, ORN, NOT, ADD, SUB, SHL, USHR, SRI,
  SLI, EXT, REV32, REV64, ZIP1, ZIP2, TRN1, TRN2, UZP1, UZP2, TBL, UMULL,
  UMLAL, PMULL, MUL, MLA, MLS, SQDMULH, UMIN), and the cryptographic ones
  (AESE, AESD, AESMC, AESIMC, SHA1C, SHA1P, SHA1M, SHA1H, SHA1SU0, SHA1SU1,
  SHA256H, SHA256H2, SHA256SU0, SHA256SU1, SHA512H, SHA512H2, SHA512SU0,
  SHA512SU1, EOR3, BCAX, RAX1, XAR) are all among those whose timing Arm specifies to be
  independent of their data when PSTATE.DIT is 1 (DDI 0487, "About
  PSTATE.DIT"). As above, the code does not set PSTATE.DIT.
-/

namespace VG.AArch64

inductive Reg
  | x0 | x1 | x2 | x3 | x4 | x5 | x6 | x7 | x8 | x9 | x10 | x11 | x12 | x13 | x14 | x15
  | x16 | x17 | x19 | x20 | x21 | x22 | x23 | x24 | x25 | x26 | x27 | x28 | x30
  deriving DecidableEq, Repr, Inhabited

/-- The SIMD and floating-point registers, other than `v8`–`v15` (see above). -/
inductive VReg
  | v0 | v1 | v2 | v3 | v4 | v5 | v6 | v7
  | v16 | v17 | v18 | v19 | v20 | v21 | v22 | v23 | v24 | v25 | v26 | v27 | v28 | v29 | v30 | v31
  deriving DecidableEq, Repr, Inhabited

/-- Operand size: 32-bit (`w` registers) or 64-bit (`x` registers). -/
inductive Size | w | x
  deriving DecidableEq, Repr

abbrev Size.bits : Size → Nat
  | .w => 32
  | .x => 64

structure State where
  gpr : Reg → BitVec 64
  sp : BitVec 64
  /-- PSTATE.C: unsigned carry, or no borrow after subtraction. -/
  c : Bool := false
  /-- The SIMD and floating-point registers (`V[n]`, 128 bits). -/
  v : VReg → BitVec 128 := fun _ => 0
  mem : Mem
  /-- Regions the code may read (in addition to `wr`). -/
  rd : List Region
  /-- Regions the code may read and write. -/
  wr : List Region
  /-- Values the model does not know, used in order: the return address each
  call stores and, on the ARM targets, what a linker veneer may leave in the
  intra-procedure-call scratch registers (see `TCB/Code.lean`). -/
  unknowns : Nat → BitVec 64 := fun _ => 0

inductive LogicOp | and | orr | eor
  deriving DecidableEq, Repr

/-- The arrangement of a vector of 32-bit (`.4s`) or 64-bit (`.2d`) lanes. -/
inductive VArr | s4 | d2
  deriving DecidableEq, Repr

/-- The size of a lane of an arrangement. -/
abbrev VArr.esize : VArr → Nat
  | .s4 => 32
  | .d2 => 64

/-- Bitwise operations on whole vectors (`.16b`). -/
inductive VLogicOp | and | orr | eor | bic | orn
  deriving DecidableEq, Repr

/-- Shifts of each lane by an immediate. -/
inductive VShiftOp | shl | ushr | sri | sli
  deriving DecidableEq, Repr

/-- Permutations of the lanes of two vectors. -/
inductive VPermOp | zip1 | zip2 | trn1 | trn2 | uzp1 | uzp2
  deriving DecidableEq, Repr

/-- Reversals of the elements within each container: `rev32 .16b` (bytes in
each word), `rev32 .8h` (halfwords in each word), `rev64 .16b` (bytes in each
doubleword), `rev64 .4s` (words in each doubleword). -/
inductive VRevOp | rev32b | rev32h | rev64b | rev64s
  deriving DecidableEq, Repr

/-- The functions of SHA1C (`SHAchoose`), SHA1P (`SHAparity`) and SHA1M
(`SHAmajority`). -/
inductive Sha1Op | c | p | m
  deriving DecidableEq, Repr

/-- AdvSIMD and cryptographic instructions that write only a vector
register (and access no memory). -/
inductive VOp
  /-- `mov vd.16b, vn.16b` (alias of ORR (vector, register) with both sources `n`) -/
  | mov (d n : VReg)
  /-- `movi vd.2d, #0` -/
  | movi0 (d : VReg)
  /-- `dup vd.4s, wn` / `dup vd.2d, xn` (DUP (general)) -/
  | dup (a : VArr) (d : VReg) (n : Reg)
  /-- `mov vd.s[i], wn` / `mov vd.d[i], xn` (alias of INS (general)) -/
  | ins (a : VArr) (d : VReg) (i : Nat) (n : Reg)
  /-- `dup sd, vn.s[i]` (DUP (element), scalar) -/
  | dupS (d n : VReg) (i : Nat)
  /-- `and`/`orr`/`eor`/`bic`/`orn vd.16b, vn.16b, vm.16b` -/
  | logic (op : VLogicOp) (d n m : VReg)
  /-- `not vd.16b, vn.16b` -/
  | not (d n : VReg)
  /-- `add vd.<a>, vn.<a>, vm.<a>` (ADD (vector)) -/
  | add (a : VArr) (d n m : VReg)
  /-- `sub vd.<a>, vn.<a>, vm.<a>` (SUB (vector)) -/
  | sub (a : VArr) (d n m : VReg)
  /-- `shl`/`ushr`/`sri`/`sli vd.<a>, vn.<a>, #sh` -/
  | shift (op : VShiftOp) (a : VArr) (d n : VReg) (sh : Nat)
  /-- `ext vd.16b, vn.16b, vm.16b, #imm` -/
  | ext (d n m : VReg) (imm : Nat)
  /-- `rev32`/`rev64 vd.<T>, vn.<T>` -/
  | rev (op : VRevOp) (d n : VReg)
  /-- `zip1`/`zip2`/`trn1`/`trn2`/`uzp1`/`uzp2 vd.<a>, vn.<a>, vm.<a>` -/
  | perm (op : VPermOp) (a : VArr) (d n m : VReg)
  /-- `tbl vd.16b, {vn.16b}, vm.16b` (a table of one register) -/
  | tbl (d n m : VReg)
  /-- `umull vd.2d, vn.2s, vm.2s`, or `umull2 vd.2d, vn.4s, vm.4s` if `hi` -/
  | umull (hi : Bool) (d n m : VReg)
  /-- `umlal vd.2d, vn.2s, vm.2s`, or `umlal2 vd.2d, vn.4s, vm.4s` if `hi` -/
  | umlal (hi : Bool) (d n m : VReg)
  /-- `mul vd.4s, vn.4s, vm.4s` (MUL (vector)) -/
  | mul (d n m : VReg)
  /-- `mla vd.4s, vn.4s, vm.4s` (MLA (vector)) -/
  | mla (d n m : VReg)
  /-- `mls vd.4s, vn.4s, vm.4s` (MLS (vector)) -/
  | mls (d n m : VReg)
  /-- `sqdmulh vd.4s, vn.4s, vm.4s` (SQDMULH (vector)) -/
  | sqdmulh (d n m : VReg)
  /-- `umin vd.4s, vn.4s, vm.4s` -/
  | umin (d n m : VReg)
  /-- `pmull vd.1q, vn.1d, vm.1d`, or `pmull2 vd.1q, vn.2d, vm.2d` if `hi` -/
  | pmull (hi : Bool) (d n m : VReg)
  /-- `aese vd.16b, vn.16b` -/
  | aese (d n : VReg)
  /-- `aesd vd.16b, vn.16b` -/
  | aesd (d n : VReg)
  /-- `aesmc vd.16b, vn.16b` -/
  | aesmc (d n : VReg)
  /-- `aesimc vd.16b, vn.16b` -/
  | aesimc (d n : VReg)
  /-- `sha1c`/`sha1p`/`sha1m qd, sn, vm.4s` -/
  | sha1 (op : Sha1Op) (d n m : VReg)
  /-- `sha1h sd, sn` -/
  | sha1h (d n : VReg)
  /-- `sha1su0 vd.4s, vn.4s, vm.4s` -/
  | sha1su0 (d n m : VReg)
  /-- `sha1su1 vd.4s, vn.4s` -/
  | sha1su1 (d n : VReg)
  /-- `sha256h qd, qn, vm.4s` -/
  | sha256h (d n m : VReg)
  /-- `sha256h2 qd, qn, vm.4s` -/
  | sha256h2 (d n m : VReg)
  /-- `sha256su0 vd.4s, vn.4s` -/
  | sha256su0 (d n : VReg)
  /-- `sha256su1 vd.4s, vn.4s, vm.4s` -/
  | sha256su1 (d n m : VReg)
  /-- `sha512h qd, qn, vm.2d` -/
  | sha512h (d n m : VReg)
  /-- `sha512h2 qd, qn, vm.2d` -/
  | sha512h2 (d n m : VReg)
  /-- `sha512su0 vd.2d, vn.2d` -/
  | sha512su0 (d n : VReg)
  /-- `sha512su1 vd.2d, vn.2d, vm.2d` -/
  | sha512su1 (d n m : VReg)
  /-- `eor3 vd.16b, vn.16b, vm.16b, va.16b` -/
  | eor3 (d n m a : VReg)
  /-- `bcax vd.16b, vn.16b, vm.16b, va.16b` -/
  | bcax (d n m a : VReg)
  /-- `rax1 vd.2d, vn.2d, vm.2d` -/
  | rax1 (d n m : VReg)
  /-- `xar vd.2d, vn.2d, vm.2d, #imm` -/
  | xar (d n m : VReg) (imm : Nat)
  deriving DecidableEq, Repr

inductive Instr
  /-- `add d, n, m` (ADD (shifted register), no shift) -/
  | add (sz : Size) (d n m : Reg)
  /-- `sub d, n, m` (SUB (shifted register), no shift) -/
  | sub (sz : Size) (d n m : Reg)
  /-- ADDS (shifted register), no shift; writes the carry flag. -/
  | adds (sz : Size) (d n m : Reg)
  /-- ADCS: add both operands and PSTATE.C, writing the carry flag. -/
  | adcs (sz : Size) (d n m : Reg)
  /-- SUBS (shifted register), no shift; C is the no-borrow flag. -/
  | subs (sz : Size) (d n m : Reg)
  /-- SBCS: subtract the second operand and NOT(PSTATE.C). -/
  | sbcs (sz : Size) (d n m : Reg)
  /-- `add d, n, #imm` (ADD (immediate), `imm < 4096`, no shift) -/
  | addImm (sz : Size) (d n : Reg) (imm : Nat)
  /-- `sub d, n, #imm` (SUB (immediate), `imm < 4096`, no shift) -/
  | subImm (sz : Size) (d n : Reg) (imm : Nat)
  /-- `and`/`orr`/`eor d, n, m` (shifted register, no shift) -/
  | logic (op : LogicOp) (sz : Size) (d n m : Reg)
  /-- `ror d, n, #sh` (alias of EXTR d, n, n, #sh), `sh < size` -/
  | ror (sz : Size) (d n : Reg) (sh : Nat)
  /-- `lsr d, n, #sh` (alias of UBFM), `sh < size` -/
  | lsr (sz : Size) (d n : Reg) (sh : Nat)
  /-- `lsl d, n, #sh` (LSL (immediate), alias of UBFM), `sh < size` -/
  | lsl (sz : Size) (d n : Reg) (sh : Nat)
  /-- `madd d, n, m, a` (MADD): `a + n * m`, modulo `2 ^ size` -/
  | madd (sz : Size) (d n m a : Reg)
  /-- `mul d, n, m` (MUL, the alias of MADD with the zero register as the
  addend): `n * m`, modulo `2 ^ size` -/
  | mul (sz : Size) (d n m : Reg)
  /-- UMULH: bits 127:64 of the unsigned 64-by-64-bit product. -/
  | umulh (d n m : Reg)
  /-- `rev wd, wn` (REV, 32-bit): reverse the bytes of the low 32 bits -/
  | rev32 (d n : Reg)
  /-- `rev xd, xn` (REV, 64-bit): reverse the bytes of all 64 bits -/
  | rev (d n : Reg)
  /-- `movz d, #imm, lsl #(16 * hw)` -/
  | movz (sz : Size) (d : Reg) (imm : BitVec 16) (hw : Nat)
  /-- `movk d, #imm, lsl #(16 * hw)` -/
  | movk (sz : Size) (d : Reg) (imm : BitVec 16) (hw : Nat)
  /-- `ldr t, [n, #off]` (LDR (immediate), unsigned offset: a multiple of the
  access size, less than 4096 times it) -/
  | ldr (sz : Size) (t n : Reg) (off : Nat)
  /-- `str t, [n, #off]` (STR (immediate), unsigned offset, as for `ldr`) -/
  | str (sz : Size) (t n : Reg) (off : Nat)
  /-- `ldrb wt, [n, #off]` (LDRB (immediate), unsigned offset, `off < 4096`):
  the byte, zero-extended into the 64-bit register -/
  | ldrb (t n : Reg) (off : Nat)
  /-- `strb wt, [n, #off]` (STRB (immediate), unsigned offset, `off < 4096`):
  the low byte of `t` -/
  | strb (t n : Reg) (off : Nat)
  /-- `str xr, [sp, #-16]!` (STR (immediate), 64-bit, pre-index): the push
  of a frame of 16 bytes (see `push`) -/
  | push (r : Reg)
  /-- `ldr xr, [sp], #16` (LDR (immediate), 64-bit, post-index): the pop of a
  frame of 16 bytes (see `pop`) -/
  | pop (r : Reg)
  /-- `ldr xt, [sp, #off]` (LDR (immediate), 64-bit, unsigned offset, base
  register SP: a multiple of 8, less than 32768) -/
  | ldrSp (t : Reg) (off : Nat)
  /-- An AdvSIMD or cryptographic instruction that writes only a vector register. -/
  | vop (op : VOp)
  /-- `ldr qt, [n, #off]` (LDR (immediate, SIMD&FP), 128-bit, unsigned offset:
  a multiple of 16, less than 65536) -/
  | ldrq (t : VReg) (n : Reg) (off : Nat)
  /-- `str qt, [n, #off]` (STR (immediate, SIMD&FP), 128-bit, unsigned offset,
  as for `ldrq`) -/
  | strq (t : VReg) (n : Reg) (off : Nat)
  /-- `umov wd, vn.s[i]` / `umov xd, vn.d[i]` (UMOV) -/
  | umov (sz : Size) (d : Reg) (n : VReg) (i : Nat)
  deriving DecidableEq, Repr

/-- Branch conditions. -/
inductive Cond
  /-- `cbz r, …`: the register (of the given size) is zero -/
  | zero (sz : Size) (r : Reg)
  /-- `cbnz r, …`: the register (of the given size) is not zero -/
  | nonzero (sz : Size) (r : Reg)
  deriving DecidableEq, Repr

namespace State

/-- Read a register at the operand size (`W[n]` or `X[n]`). -/
def read (s : State) (sz : Size) (r : Reg) : BitVec sz.bits := (s.gpr r).setWidth sz.bits

/-- Write a register at the operand size, zero-extending a 32-bit value. -/
def write (s : State) (sz : Size) (r : Reg) (v : BitVec sz.bits) : State :=
  { s with gpr := fun r' => if r' = r then v.setWidth 64 else s.gpr r' }

/-- DDI 0487 C6.2, ADDS/ADCS/SUBS/SBCS and shared pseudocode AddWithCarry:
the result is the low `size` bits of `UInt(a) + UInt(b) + UInt(carry)`;
C says that the unsigned sum does not fit. The other NZCV bits are not
observable in this model. SUBS uses `(a, NOT(b), 1)` and SBCS uses
`(a, NOT(b), PSTATE.C)`. All four are baseline A64 instructions.
https://developer.arm.com/documentation/ddi0487/latest -/
def addWithCarry (s : State) (sz : Size) (d : Reg)
    (a b : BitVec sz.bits) (carry : Bool) : State :=
  { s.write sz d (a + b + BitVec.ofNat sz.bits carry.toNat) with
    c := decide (2 ^ sz.bits ≤ a.toNat + b.toNat + carry.toNat) }

/-- Write a vector register (`V[n] = value`, 128 bits). -/
def setV (s : State) (r : VReg) (x : BitVec 128) : State :=
  { s with v := fun r' => if r' = r then x else s.v r' }

/-- Load `n` bytes, faulting if not permitted. -/
def load (s : State) (a : Addr) (n : Nat) : Option (BitVec (8 * n)) :=
  if InRegions (s.rd ++ s.wr) a n then some (s.mem.read a n) else none

/-- Store `n` bytes, faulting if not permitted. -/
def store (s : State) (a : Addr) (n : Nat) (v : BitVec (8 * n)) : Option State :=
  if InRegions s.wr a n then some { s with mem := s.mem.write a n v } else none

end State

abbrev Size.bytes : Size → Nat
  | .w => 4
  | .x => 8

theorem Size.bits_eq (sz : Size) : sz.bits = 8 * sz.bytes := by cases sz <;> rfl

/-- The address of `[n, #off]` for an access of `bytes` bytes, if `off` is
encodable (DDI 0487 C6.2, "LDR (immediate)"/"STR (immediate)" and "LDRB
(immediate)"/"STRB (immediate)", unsigned offset: `offset = LSL(imm12,
scale)`, where `bytes = 2 ^ scale`, and `scale = 0` for the byte forms). -/
def addr (s : State) (bytes : Nat) (n : Reg) (off : Nat) : Option Addr :=
  if off % bytes = 0 ∧ off < 4096 * bytes then some (s.gpr n + BitVec.ofNat 64 off)
  else none

/-- `REV` (32-bit): `result<7:0> = X<31:24>` etc. (DDI 0487 C6.2, "REV"). -/
def rev32 (a : BitVec 32) : BitVec 32 :=
  a.extractLsb' 0 8 ++ a.extractLsb' 8 8 ++ a.extractLsb' 16 8 ++ a.extractLsb' 24 8

/-- `REV` (64-bit): `Reverse(X[n, 64], 8)`, i.e. `result<7:0> = X<63:56>`,
`result<15:8> = X<55:48>`, …, `result<63:56> = X<7:0>` (DDI 0487 C6.2,
"REV"). -/
def rev64 (a : BitVec 64) : BitVec 64 :=
  a.extractLsb' 0 8 ++ a.extractLsb' 8 8 ++ a.extractLsb' 16 8 ++ a.extractLsb' 24 8 ++
    a.extractLsb' 32 8 ++ a.extractLsb' 40 8 ++ a.extractLsb' 48 8 ++ a.extractLsb' 56 8

/-! ### AdvSIMD and cryptographic instructions

The semantics of `VOp`, transcribing DDI 0487 C7.2 (lanes as in
`TCB/AArch64/Simd.lean`: lane `e` of size `esize` is bits
`(e+1)*esize-1 : e*esize`). -/

/-- `x` with lane `i` of size `w` (bits `(i+1)*w-1 : i*w`) replaced by `v`. -/
def setLane (x : BitVec 128) (w i : Nat) (v : BitVec w) : BitVec 128 :=
  (x &&& ~~~((BitVec.allOnes w).setWidth 128 <<< (w * i))) ||| (v.setWidth 128 <<< (w * i))

/-- The vector whose lane `e` of the arrangement `a` is `f esize (lane e of x)
(lane e of y)`, for a function `f` on lanes of any size. -/
def VArr.map2 (a : VArr) (f : (w : Nat) → BitVec w → BitVec w → BitVec w)
    (x y : BitVec 128) : BitVec 128 :=
  match a with
  | .s4 => ofVWords (f 32 (vword x 0) (vword y 0)) (f 32 (vword x 1) (vword y 1))
      (f 32 (vword x 2) (vword y 2)) (f 32 (vword x 3) (vword y 3))
  | .d2 => ofVDwords (f 64 (vdword x 0) (vdword y 0)) (f 64 (vdword x 1) (vdword y 1))

/-- The lanes of `x` in the arrangement `a`, lowest first. -/
def VArr.lanes (a : VArr) (x : BitVec 128) : List (BitVec 128) :=
  match a with
  | .s4 => [(vword x 0).setWidth 128, (vword x 1).setWidth 128, (vword x 2).setWidth 128,
      (vword x 3).setWidth 128]
  | .d2 => [(vdword x 0).setWidth 128, (vdword x 1).setWidth 128]

/-- The vector of the arrangement `a` whose lanes are `ls`, lowest first. -/
def VArr.ofLanes (a : VArr) (ls : List (BitVec 128)) : BitVec 128 :=
  let l (e : Nat) : BitVec 128 := ls.getD e 0
  match a with
  | .s4 => ofVWords ((l 0).setWidth 32) ((l 1).setWidth 32) ((l 2).setWidth 32) ((l 3).setWidth 32)
  | .d2 => ofVDwords ((l 0).setWidth 64) ((l 1).setWidth 64)

/-- DDI 0487 C7.2, "ZIP1", "ZIP2", "TRN1", "TRN2", "UZP1", "UZP2", with
`operand1 = V[n]` (lanes `n`) and `operand2 = V[m]` (lanes `m`), and `pairs`
the number of lane pairs (`elements / 2`):
* ZIP1/ZIP2: `base = part * pairs; for p = 0 to pairs-1: Elem[result, 2*p+0]
  = Elem[operand1, base+p]; Elem[result, 2*p+1] = Elem[operand2, base+p]`
  (`part` 0 or 1);
* TRN1/TRN2: `for p = 0 to pairs-1: Elem[result, 2*p+0] = Elem[operand1,
  2*p+part]; Elem[result, 2*p+1] = Elem[operand2, 2*p+part]`;
* UZP1/UZP2: `zipped = operand2:operand1; for e = 0 to elements-1:
  Elem[result, e] = Elem[zipped, 2*e+part]`. -/
def VPermOp.eval (op : VPermOp) (a : VArr) (x y : BitVec 128) : BitVec 128 :=
  let n := a.lanes x
  let m := a.lanes y
  let pairs := n.length / 2
  let g (l : List (BitVec 128)) (i : Nat) : BitVec 128 := l.getD i 0
  a.ofLanes <| match op with
  | .zip1 => (List.range pairs).flatMap fun p => [g n p, g m p]
  | .zip2 => (List.range pairs).flatMap fun p => [g n (pairs + p), g m (pairs + p)]
  | .trn1 => (List.range pairs).flatMap fun p => [g n (2 * p), g m (2 * p)]
  | .trn2 => (List.range pairs).flatMap fun p => [g n (2 * p + 1), g m (2 * p + 1)]
  | .uzp1 => (List.range n.length).map fun e => g (n ++ m) (2 * e)
  | .uzp2 => (List.range n.length).map fun e => g (n ++ m) (2 * e + 1)

/-- The vector whose word `e` is `f` of word `e` of `x`, `y` and `z`. -/
def mapWords3 (f : BitVec 32 → BitVec 32 → BitVec 32 → BitVec 32) (x y z : BitVec 128) :
    BitVec 128 :=
  ofVWords (f (vword x 0) (vword y 0) (vword z 0)) (f (vword x 1) (vword y 1) (vword z 1))
    (f (vword x 2) (vword y 2) (vword z 2)) (f (vword x 3) (vword y 3) (vword z 3))

/-- One lane of SQDMULH (`.4s`), DDI 0487 C7.2, "SQDMULH (vector)":
`element1 = SInt(Elem[operand1, e]); element2 = SInt(Elem[operand2, e]);
product = 2 * element1 * element2; product = RShr(product, esize, FALSE)`
(`product >> 32`, rounding towards minus infinity); `(Elem[result, e], sat)
= SignedSatQ(product, esize)`, which saturates, and sets FPSR.QC, exactly
when both elements are `-2 ^ 31`. `none` there: the model faults rather
than saturate. -/
def sqdmulhLane (a b : BitVec 32) : Option (BitVec 32) :=
  if a = 0x80000000#32 ∧ b = 0x80000000#32 then none
  else some (BitVec.ofInt 32 ((2 * a.toInt * b.toInt) >>> 32))

/-- DDI 0487 C7.2, "REV32" and "REV64" (`Reverse` of the elements within
each container): byte `i` of the result is byte `rev i` of the operand. -/
def VRevOp.eval (op : VRevOp) (x : BitVec 128) : BitVec 128 :=
  ofVBytes fun i => vbyte x <| match op with
    | .rev32b => 4 * (i / 4) + (3 - i % 4)
    | .rev32h => 4 * (i / 4) + (i % 4 + 2) % 4
    | .rev64b => 8 * (i / 8) + (7 - i % 8)
    | .rev64s => 8 * (i / 8) + (i % 8 + 4) % 8

/-- Whether the shift `sh` is encodable for `op` on lanes of `esize` bits:
`0 ≤ sh < esize` for SHL and SLI, `1 ≤ sh ≤ esize` for USHR and SRI. -/
def VShiftOp.ok (op : VShiftOp) (esize sh : Nat) : Bool :=
  match op with
  | .shl | .sli => sh < esize
  | .ushr | .sri => 1 ≤ sh && sh ≤ esize

/-- DDI 0487 C7.2, the shifts by an immediate of one lane `a` of the
destination and `b` of the source (`operand = V[n]`, `operand2 = V[d]`):
* SHL: `Elem[result, e] = LSL(Elem[operand, e], shift)`;
* USHR: `Elem[result, e] = LSR(Elem[operand, e], shift)` (the unsigned,
  unrounded form of `ShiftRight`);
* SRI: `mask = LSR(Ones(esize), shift); shifted = LSR(Elem[operand, e],
  shift); Elem[result, e] = (Elem[operand2, e] AND NOT(mask)) OR shifted`;
* SLI: `mask = LSL(Ones(esize), shift); shifted = LSL(Elem[operand, e],
  shift); Elem[result, e] = (Elem[operand2, e] AND NOT(mask)) OR shifted`. -/
def VShiftOp.eval (op : VShiftOp) (sh w : Nat) (a b : BitVec w) : BitVec w :=
  match op with
  | .shl => b <<< sh
  | .ushr => b >>> sh
  | .sri => (a &&& ~~~(BitVec.allOnes w >>> sh)) ||| (b >>> sh)
  | .sli => (a &&& ~~~(BitVec.allOnes w <<< sh)) ||| (b <<< sh)

/-- The function of SHA1C, SHA1P or SHA1M. -/
def Sha1Op.f : Sha1Op → BitVec 32 → BitVec 32 → BitVec 32 → BitVec 32
  | .c => shaChoose
  | .p => shaParity
  | .m => shaMajority

/-- The new value of the destination, given the state. DDI 0487 C7.2:
* "MOV (vector)" = "ORR (vector, register)" with both sources `n`: `V[n]`;
  "MOVI" (64-bit variant, `imm = 0`): zeros;
* "DUP (general)": `element = X[n, esize]`, in every lane; "INS (general)":
  `element = X[n, esize]; result = V[d]; Elem[result, index, esize] =
  element`; "DUP (element)", scalar: `element = Elem[V[n], index, esize];
  V[d] = element` (the other bits of `V[d]` zero);
* "AND", "ORR", "EOR", "BIC" (`operand1 AND NOT(operand2)`), "ORN"
  (`operand1 OR NOT(operand2)`) and "NOT" (vector, `.16b`);
* "ADD (vector)", "SUB (vector)": lane-wise, modulo `2 ^ esize`;
* the shifts (`VShiftOp.eval`), the permutations (`VPermOp.eval`) and the
  reversals (`VRevOp.eval`);
* "EXT": `concat = operand2:operand1; result = concat<position+127:position>`
  with `operand1 = V[n]`, `operand2 = V[m]`, `position = imm * 8`;
* "TBL" (one register): `index = UInt(Elem[indices, i, 8]); if index < 16
  then Elem[result, i, 8] = Elem[table, index, 8] else 0`, with `table =
  V[n]`, `indices = V[m]`;
* "UMULL", "UMULL2", "UMLAL", "UMLAL2": `part` 0, or 1 for the `2` forms,
  selects the lower or upper half of the sources: `element1 =
  Elem[operand1, e, 32]; element2 = Elem[operand2, e, 32]; product =
  element1 * element2` (unsigned, 64 bits), then `Elem[result, e, 64] =
  product` (UMULL) or `Elem[operand3, e, 64] + product` (UMLAL, `operand3 =
  V[d]`);
* "MUL (vector)", "MLA (vector)", "MLS (vector)" (`.4s`): `product =
  (UInt(element1) * UInt(element2))<esize-1:0>`, and `Elem[result, e] =
  product`, `Elem[operand3, e] + product` or `Elem[operand3, e] - product`
  (`operand3 = V[d]`), modulo `2 ^ 32`;
* "SQDMULH (vector)" (`.4s`): `sqdmulhLane` in each lane, faulting if any
  would saturate;
* "UMIN" (`.4s`): `Elem[result, e] = Min(UInt(element1), UInt(element2))`;
* "PMULL", "PMULL2" (`.1q`): `Elem[result, 0, 128] =
  PolynomialMult(Elem[operand1, part, 64], Elem[operand2, part, 64])`;
* "AESE": `AESSubBytes(AESShiftRows(operand1 EOR operand2))`; "AESD":
  `AESInvSubBytes(AESInvShiftRows(operand1 EOR operand2))`, with `operand1
  = V[d]`, `operand2 = V[n]`; "AESMC": `AESMixColumns(V[n])`; "AESIMC":
  `AESInvMixColumns(V[n])`;
* "SHA1C", "SHA1P", "SHA1M": `sha1Hash`; "SHA1H": `V[d] = ROL(V[n]<31:0>,
  30)` (the other bits zero); "SHA1SU0", "SHA1SU1": `sha1Su0`, `sha1Su1`;
* "SHA256H": `SHA256hash(V[d], V[n], V[m], TRUE)`; "SHA256H2":
  `SHA256hash(V[n], V[d], V[m], FALSE)`; "SHA256SU0", "SHA256SU1":
  `sha256Su0`, `sha256Su1`;
* "SHA512H", "SHA512H2", "SHA512SU0", "SHA512SU1": `sha512H`, `sha512H2`,
  `sha512Su0`, `sha512Su1`;
* "EOR3": `Vn EOR Vm EOR Va`; "BCAX": `Vn EOR (Vm AND NOT(Va))`; "RAX1":
  `Elem[Vd, e, 64] = Elem[Vn, e, 64] EOR ROL(Elem[Vm, e, 64], 1)`; "XAR":
  `Elem[Vd, e, 64] = ROR(Elem[Vn, e, 64] EOR Elem[Vm, e, 64], imm6)`.

Immediates that are not encodable (an out-of-range shift, lane index or
EXT position) make the instruction fault. -/
def VOp.eval (s : State) : VOp → Option (VReg × BitVec 128)
  | .mov d n => some (d, s.v n)
  | .movi0 d => some (d, 0)
  | .dup .s4 d n => let w := (s.gpr n).setWidth 32; some (d, ofVWords w w w w)
  | .dup .d2 d n => some (d, ofVDwords (s.gpr n) (s.gpr n))
  | .ins .s4 d i n => if i < 4 then some (d, setLane (s.v d) 32 i ((s.gpr n).setWidth 32)) else none
  | .ins .d2 d i n => if i < 2 then some (d, setLane (s.v d) 64 i (s.gpr n)) else none
  | .dupS d n i => if i < 4 then some (d, (vword (s.v n) i).setWidth 128) else none
  | .logic op d n m =>
    let a := s.v n
    let b := s.v m
    some (d, match op with
      | .and => a &&& b | .orr => a ||| b | .eor => a ^^^ b | .bic => a &&& ~~~b
      | .orn => a ||| ~~~b)
  | .not d n => some (d, ~~~(s.v n))
  | .add a d n m => some (d, a.map2 (fun _ x y => x + y) (s.v n) (s.v m))
  | .sub a d n m => some (d, a.map2 (fun _ x y => x - y) (s.v n) (s.v m))
  | .shift op a d n sh =>
    if op.ok a.esize sh then some (d, a.map2 (fun w x y => op.eval sh w x y) (s.v d) (s.v n))
    else none
  | .ext d n m imm =>
    if imm < 16 then some (d, ((s.v m ++ s.v n) >>> (imm * 8)).extractLsb' 0 128) else none
  | .rev op d n => some (d, op.eval (s.v n))
  | .perm op a d n m => some (d, op.eval a (s.v n) (s.v m))
  | .tbl d n m => some (d, ofVBytes fun i =>
      let idx := (vbyte (s.v m) i).toNat
      if idx < 16 then vbyte (s.v n) idx else 0)
  | .umull hi d n m =>
    let p := if hi then 2 else 0
    let prod (e : Nat) : BitVec 64 :=
      (vword (s.v n) (p + e)).setWidth 64 * (vword (s.v m) (p + e)).setWidth 64
    some (d, ofVDwords (prod 0) (prod 1))
  | .umlal hi d n m =>
    let p := if hi then 2 else 0
    let prod (e : Nat) : BitVec 64 :=
      (vword (s.v n) (p + e)).setWidth 64 * (vword (s.v m) (p + e)).setWidth 64
    some (d, ofVDwords (vdword (s.v d) 0 + prod 0) (vdword (s.v d) 1 + prod 1))
  | .mul d n m => some (d, VArr.s4.map2 (fun _ x y => x * y) (s.v n) (s.v m))
  | .mla d n m => some (d, mapWords3 (fun a x y => a + x * y) (s.v d) (s.v n) (s.v m))
  | .mls d n m => some (d, mapWords3 (fun a x y => a - x * y) (s.v d) (s.v n) (s.v m))
  | .sqdmulh d n m =>
    let r (e : Nat) := sqdmulhLane (vword (s.v n) e) (vword (s.v m) e)
    match r 0, r 1, r 2, r 3 with
    | some w0, some w1, some w2, some w3 => some (d, ofVWords w0 w1 w2 w3)
    | _, _, _, _ => none
  | .umin d n m =>
    some (d, VArr.s4.map2 (fun _ x y => if x.toNat ≤ y.toNat then x else y) (s.v n) (s.v m))
  | .pmull hi d n m =>
    let p := if hi then 1 else 0
    some (d, polyMul (vdword (s.v n) p) (vdword (s.v m) p))
  | .aese d n => some (d, aesMapBytes aesSbox (aesShiftRows (s.v d ^^^ s.v n)))
  | .aesd d n => some (d, aesMapBytes aesInvSbox (aesInvShiftRows (s.v d ^^^ s.v n)))
  | .aesmc d n => some (d, aesMixColumns (s.v n))
  | .aesimc d n => some (d, aesInvMixColumns (s.v n))
  | .sha1 op d n m => some (d, sha1Hash op.f (s.v d) (vword (s.v n) 0) (s.v m))
  | .sha1h d n => some (d, ((vword (s.v n) 0).rotateLeft 30).setWidth 128)
  | .sha1su0 d n m => some (d, sha1Su0 (s.v d) (s.v n) (s.v m))
  | .sha1su1 d n => some (d, sha1Su1 (s.v d) (s.v n))
  | .sha256h d n m => some (d, sha256Hash (s.v d) (s.v n) (s.v m) true)
  | .sha256h2 d n m => some (d, sha256Hash (s.v n) (s.v d) (s.v m) false)
  | .sha256su0 d n => some (d, sha256Su0 (s.v d) (s.v n))
  | .sha256su1 d n m => some (d, sha256Su1 (s.v d) (s.v n) (s.v m))
  | .sha512h d n m => some (d, sha512H (s.v d) (s.v n) (s.v m))
  | .sha512h2 d n m => some (d, sha512H2 (s.v d) (s.v n) (s.v m))
  | .sha512su0 d n => some (d, sha512Su0 (s.v d) (s.v n))
  | .sha512su1 d n m => some (d, sha512Su1 (s.v d) (s.v n) (s.v m))
  | .eor3 d n m a => some (d, s.v n ^^^ s.v m ^^^ s.v a)
  | .bcax d n m a => some (d, s.v n ^^^ (s.v m &&& ~~~(s.v a)))
  | .rax1 d n m => some (d, VArr.d2.map2 (fun _ x y => x ^^^ y.rotateLeft 1) (s.v n) (s.v m))
  | .xar d n m imm =>
    if imm < 64 then some (d, VArr.d2.map2 (fun _ x y => (x ^^^ y).rotateRight imm) (s.v n) (s.v m))
    else none

/-- Semantics, transcribing DDI 0487 C6.2:
* "ADD (shifted register)", "ADD (immediate)", "SUB (immediate)": the
  result of `AddWithCarry` (the flags are not set by these forms);
* "SUB (shifted register)": `AddWithCarry(operand1, NOT(operand2), '1')`,
  i.e. `n - m` modulo `2 ^ size` (the flags are not set by this form);
* "AND/ORR/EOR (shifted register)";
* "ROR (immediate)" = "EXTR" with both sources `n`: `(n:n)<sh+size-1:sh>`,
  a rotation right by `sh`;
* "LSR (immediate)" = "UBFM": a logical shift right by `sh`;
* "LSL (immediate)" = "UBFM" with `immr = -sh MOD size`, `imms = size - 1 -
  sh`: a logical shift left by `sh` (the bits shifted out are lost, zeros
  shifted in);
* "MADD": `result = UInt(operand3) + (UInt(operand1) * UInt(operand2));
  X[d, destsize] = result<destsize-1:0>`, with `operand1 = X[n]`, `operand2
  = X[m]`, `operand3 = X[a]` at the operand size; "MUL" = "MADD" with `a` the
  zero register, so `operand3 = 0` (the flags are not set by either);
* "REV" (32- and 64-bit); "MOVZ": `imm` at bit `16 * hw` of zeros; "MOVK":
  `imm` into bits `16 * hw + 15 : 16 * hw` of the destination, the others
  unchanged (`hw < 2` for 32-bit, `hw < 4` for 64-bit);
* "LDR (immediate)": the loaded value is zero-extended; "STR (immediate)":
  the low `size` bits are stored;
* "LDR (immediate)" with `n == 31` (`ldrSp`): `address = SP[]`, then as
  above, `address + offset` with `offset = LSL(imm12, 3)`; `data = Mem[address,
  8]`; `X[t, 64] = data`;
* "LDRB (immediate)": `data = Mem[address, 1]; X[t, 32] = ZeroExtend(data,
  32)` (hence zero-extended to 64 bits); "STRB (immediate)": `data = X[t,
  8]; Mem[address, 1] = data`, the low byte of `t`;
* an AdvSIMD or cryptographic instruction: `VOp.eval`;
* "LDR (immediate, SIMD&FP)", "STR (immediate, SIMD&FP)" (128-bit, unsigned
  offset: `offset = LSL(imm12, 4)`): `V[t] = Mem[address, 16]` and
  `Mem[address, 16] = V[t]`;
* "UMOV": `X[d, datasize] = ZeroExtend(Elem[V[n], index, esize], datasize)`,
  with `esize = datasize` (32 or 64). -/
def exec : Instr → State → Option State
  | .add sz d n m, s => some (s.write sz d (s.read sz n + s.read sz m))
  | .sub sz d n m, s => some (s.write sz d (s.read sz n - s.read sz m))
  | .adds sz d n m, s => some (s.addWithCarry sz d (s.read sz n) (s.read sz m) false)
  | .adcs sz d n m, s => some (s.addWithCarry sz d (s.read sz n) (s.read sz m) s.c)
  | .subs sz d n m, s => some (s.addWithCarry sz d (s.read sz n) (~~~s.read sz m) true)
  | .sbcs sz d n m, s => some (s.addWithCarry sz d (s.read sz n) (~~~s.read sz m) s.c)
  | .addImm sz d n imm, s =>
    if imm < 4096 then some (s.write sz d (s.read sz n + BitVec.ofNat _ imm)) else none
  | .subImm sz d n imm, s =>
    if imm < 4096 then some (s.write sz d (s.read sz n - BitVec.ofNat _ imm)) else none
  | .logic op sz d n m, s =>
    let a := s.read sz n
    let b := s.read sz m
    some (s.write sz d (match op with | .and => a &&& b | .orr => a ||| b | .eor => a ^^^ b))
  | .ror sz d n sh, s =>
    if sh < sz.bits then some (s.write sz d ((s.read sz n).rotateRight sh)) else none
  | .lsr sz d n sh, s =>
    if sh < sz.bits then some (s.write sz d (s.read sz n >>> sh)) else none
  | .lsl sz d n sh, s =>
    if sh < sz.bits then some (s.write sz d (s.read sz n <<< sh)) else none
  | .madd sz d n m a, s => some (s.write sz d (s.read sz a + s.read sz n * s.read sz m))
  | .mul sz d n m, s => some (s.write sz d (s.read sz n * s.read sz m))
  -- DDI 0487 C6.2, UMULH: UInt(X[n]) * UInt(X[m]), bits 127:64.
  | .umulh d n m, s =>
    some (s.write .x d (BitVec.ofNat 64 ((s.gpr n).toNat * (s.gpr m).toNat / 2 ^ 64)))
  | .rev32 d n, s => some (s.write .w d (rev32 (s.read .w n)))
  | .rev d n, s => some (s.write .x d (rev64 (s.read .x n)))
  | .movz sz d imm hw, s =>
    if 16 * hw < sz.bits then some (s.write sz d (imm.setWidth sz.bits <<< (16 * hw))) else none
  | .movk sz d imm hw, s =>
    if 16 * hw < sz.bits then
      let mask : BitVec sz.bits := (0xFFFF : BitVec sz.bits) <<< (16 * hw)
      some (s.write sz d ((s.read sz d &&& ~~~mask) ||| (imm.setWidth sz.bits <<< (16 * hw))))
    else none
  | .ldr sz t n off, s =>
    (addr s sz.bytes n off).bind fun a =>
      (s.load a sz.bytes).map fun v => s.write sz t (v.setWidth sz.bits)
  | .str sz t n off, s =>
    (addr s sz.bytes n off).bind fun a => s.store a sz.bytes ((s.read sz t).setWidth (8 * sz.bytes))
  | .ldrb t n off, s =>
    (addr s 1 n off).bind fun a => (s.load a 1).map fun v => s.write .w t (v.setWidth 32)
  | .strb t n off, s =>
    (addr s 1 n off).bind fun a => s.store a 1 ((s.read .w t).setWidth 8)
  | .ldrSp t off, s =>
    if off % 8 = 0 ∧ off < 32768 then
      (s.load (s.sp + BitVec.ofNat 64 off) 8).map fun v => s.write .x t (v.setWidth 64)
    else none
  | .vop op, s => (op.eval s).map fun (d, x) => s.setV d x
  | .ldrq t n off, s => (addr s 16 n off).bind fun a => (s.load a 16).map fun x => s.setV t x
  | .strq t n off, s => (addr s 16 n off).bind fun a => s.store a 16 (s.v t)
  | .umov sz d n i, s =>
    if i * sz.bits < 128 then some (s.write sz d ((s.v n).extractLsb' (sz.bits * i) sz.bits))
    else none
  -- Only the push and pop of a frame (`push`, `pop`).
  | .push _, _ | .pop _, _ => none

def addrs : Instr → State → List Addr
  | .ldr _ _ n off, s => [s.gpr n + BitVec.ofNat 64 off]
  | .str _ _ n off, s => [s.gpr n + BitVec.ofNat 64 off]
  | .ldrb _ n off, s => [s.gpr n + BitVec.ofNat 64 off]
  | .strb _ n off, s => [s.gpr n + BitVec.ofNat 64 off]
  | .ldrq _ n off, s => [s.gpr n + BitVec.ofNat 64 off]
  | .strq _ n off, s => [s.gpr n + BitVec.ofNat 64 off]
  | .ldrSp _ off, s => [s.sp + BitVec.ofNat 64 off]
  | .push _, s => [s.sp - 16]
  | .pop _, s => [s.sp]
  | _, _ => []

/-- DDI 0487 C6.2, "CBZ"/"CBNZ": the branch is taken iff the operand is (not) zero. -/
def eval : Cond → State → Option Bool
  | .zero sz r, s => some (s.read sz r == 0)
  | .nonzero sz r, s => some (s.read sz r != 0)

/-- DDI 0487, C6.2 "BL": `X[30, 64] = PC64 + 4` (the address of the next
instruction), then the branch, possibly through a linker veneer, which may
change `x16` and `x17` (AAPCS64 §6.1.1). The return address and the values
left in `x16` and `x17` are the next three of the state's unknowns. The
fourth supplies an independent C bit: AAPCS64 §6.1.1 makes NZCV undefined
at public interfaces, and AAELF64 §5.7.7 (Call and Jump relocations) permits
veneers to corrupt it.
https://github.com/ARM-software/abi-aa/blob/main/aaelf64/aaelf64.rst -/
def call (s : State) : Option State :=
  some { s with
    gpr := fun r =>
      if r = .x30 then s.unknowns 0 else if r = .x16 then s.unknowns 1
      else if r = .x17 then s.unknowns 2 else s.gpr r
    c := (s.unknowns 3).getLsbD 0
    unknowns := fun n => s.unknowns (n + 4) }

/-- DDI 0487, C6.2 "RET" (with the default register `x30`): `target =
X[30, 64]; BranchTo(target)`. It returns after the call instruction if `x30`
is the return address the call left (`s₁`); otherwise the model faults. -/
def ret (s₁ s₂ : State) : Option State :=
  if s₂.gpr .x30 = s₁.gpr .x30 then some s₂ else none

/-- The push of a frame, DDI 0487 C6.2 "STR (immediate)", 64-bit, pre-index
(`str xr, [sp, #-16]!`): `address = SP[] + offset` with `offset = -16`;
`Mem[address, 8] = X[t]`; `SP[] = address`. The 16 bytes (the register,
then 8 bytes it does not write) become a writable region, at the head of
`wr`. Faults if the frame would wrap around the address space
(`sp < 16`).

The model grants 16 bytes but writes only the first 8, so `[sp, #8]` then
holds what memory held there before the push. That memory was below the
stack pointer, where on hardware a signal handler may change it at any
time, while the model keeps it until a store. This is harmless: the
contract says nothing of those bytes (they are in the stack below the
caller's stack pointer, `Abi.reserved`, which no buffer overlaps), so a
proof holds whatever they contain and learns nothing from reading them;
it could only rely on two reads agreeing. The only read that addresses the
stack pointer is `ldrSp`, and no emitted code reads `[sp, #n]`
(`src/asm/aarch64/`). -/
def push : Instr → State → Option State
  | .push r, s =>
    if 16 ≤ s.sp.toNat then
      let sp := s.sp - 16
      some { s with sp := sp, mem := s.mem.write sp 8 (s.gpr r), wr := ⟨sp, 16⟩ :: s.wr }
    else none
  | _, _ => none

/-- The pop of a frame, DDI 0487 C6.2 "LDR (immediate)", 64-bit, post-index
(`ldr xr, [sp], #16`): `address = SP[]`; `data = Mem[address, 8]`; `SP[] =
address + 16`; `X[t] = data`. Faults unless the stack pointer and the
writable regions are those the push left (`s₁`), whose head is the frame;
it removes the frame. -/
def pop : Instr → State → State → Option State
  | .pop r, s₁, s₂ =>
    if s₂.sp = s₁.sp ∧ s₂.wr = s₁.wr ∧ s₁.wr.head? = some ⟨s₁.sp, 16⟩ then
      some { s₂.write .x r (s₂.mem.read s₂.sp 8) with sp := s₂.sp + 16, wr := s₂.wr.tail }
    else none
  | _, _, _ => none

/-- The CPU features an instruction needs beyond the AArch64 baseline
(ARMv8.0-A with AdvSIMD, which every Rust AArch64 target assumes), named as
Rust's target features. DDI 0487 A2 ("Armv8-A architecture extensions") and
the "Is FEAT_…" condition in each instruction's decode (C7.2): FEAT_AES for
AESE, AESD, AESMC, AESIMC and FEAT_PMULL for PMULL/PMULL2 with 64-bit
sources, which Rust's `aes` feature covers together; FEAT_SHA1 for SHA1C,
SHA1P, SHA1M, SHA1H, SHA1SU0, SHA1SU1 and FEAT_SHA256 for SHA256H,
SHA256H2, SHA256SU0, SHA256SU1 (Rust's `sha2`); FEAT_SHA512 for SHA512H,
SHA512H2, SHA512SU0, SHA512SU1 and FEAT_SHA3 for EOR3, BCAX, RAX1, XAR
(Rust's `sha3`). -/
def Instr.requires : Instr → List String
  | .vop (.aese ..) | .vop (.aesd ..) | .vop (.aesmc ..) | .vop (.aesimc ..)
  | .vop (.pmull ..) => ["aes"]
  | .vop (.sha1 ..) | .vop (.sha1h ..) | .vop (.sha1su0 ..) | .vop (.sha1su1 ..)
  | .vop (.sha256h ..) | .vop (.sha256h2 ..) | .vop (.sha256su0 ..) | .vop (.sha256su1 ..) =>
    ["sha2"]
  | .vop (.sha512h ..) | .vop (.sha512h2 ..) | .vop (.sha512su0 ..) | .vop (.sha512su1 ..)
  | .vop (.eor3 ..) | .vop (.bcax ..) | .vop (.rax1 ..) | .vop (.xar ..) => ["sha3"]
  | _ => []

abbrev isa : ISA where
  State := State
  Instr := Instr
  Cond := Cond
  exec := exec
  addrs := addrs
  eval := eval
  call := call
  callAddrs _ := []
  ret := ret
  retAddrs _ := []
  -- No modelled instruction writes the stack pointer, other than the push
  -- and pop of a frame (`ldrSp` only reads it).
  writesSp _ := false
  push := push
  pop := pop
  requires := Instr.requires

end VG.AArch64
