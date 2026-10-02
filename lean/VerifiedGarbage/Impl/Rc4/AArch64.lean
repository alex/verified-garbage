import VerifiedGarbage.TCB.AArch64.Isa

/-!
# RC4 on baseline AArch64

Table lookups scan every 16-byte row, using NEON TBL on registers rather
than indexing memory with a secret. Only row addresses and the PRGA index
`i` are public. No instruction outside the baseline ISA is needed.
-/

namespace VG.Impl.Rc4.AArch64
open VG.AArch64

/-- Read one byte from the 256-byte table at `x0`, indexed by the low byte
of `x4`, into `x6`. Clobbers `x5`–`x11` and `v0`–`v2`. -/
def lookupStep : List Instr := [
  .add .x .x7 .x0 .x5, .ldrq .v0 .x7 0,
  .sub .w .x10 .x4 .x5, .vop (.dup .s4 .v1 .x10),
  .vop (.tbl .v2 .v0 .v1), .umov .w .x8 .v2 0,
  .logic .and .x .x8 .x8 .x9, .logic .orr .x .x6 .x6 .x8,
  .addImm .x .x5 .x5 16]

/-- A fixed number of rows, unrolled to avoid per-row loop control. -/
def scanRows (step : List Instr) : Nat → Prog isa
  | 0 => .block []
  | n + 1 => .seq (.block step) (scanRows step n)

/-- Scanning register-table lookup. -/
def lookup : Prog isa :=
  .seq (.block [.movz .x .x5 0 0, .movz .x .x6 0 0, .movz .x .x9 255 0])
    (scanRows lookupStep 16)

/-- Build byte indices 0..15 and the one-byte equality table. -/
def replaceSetup : List Instr := [
  .movz .w .x16 0x0101 0, .movk .w .x16 0x0101 1,
  .vop (.movi0 .v3),
  .movz .w .x10 0x0100 0, .movk .w .x10 0x0302 1, .vop (.ins .s4 .v3 0 .x10),
  .movz .w .x10 0x0504 0, .movk .w .x10 0x0706 1, .vop (.ins .s4 .v3 1 .x10),
  .movz .w .x10 0x0908 0, .movk .w .x10 0x0b0a 1, .vop (.ins .s4 .v3 2 .x10),
  .movz .w .x10 0x0d0c 0, .movk .w .x10 0x0f0e 1, .vop (.ins .s4 .v3 3 .x10),
  .vop (.movi0 .v4), .movz .w .x10 255 0, .vop (.ins .s4 .v4 0 .x10),
  .mul .w .x10 .x14 .x16, .vop (.dup .s4 .v5 .x10),
  .movz .x .x5 0 0, .movz .x .x6 0 0, .movz .x .x9 255 0]

/-- Select the original indexed byte and replace it, at fixed row addresses.
TBL of `[255, 0, …, 0]` at `lane XOR index` makes a byte equality mask. -/
def replaceStep : List Instr := [
  .add .x .x7 .x0 .x5, .ldrq .v0 .x7 0,
  .sub .w .x10 .x4 .x5, .vop (.dup .s4 .v1 .x10),
  .vop (.tbl .v2 .v0 .v1), .umov .w .x8 .v2 0,
  .logic .and .x .x8 .x8 .x9, .logic .orr .x .x6 .x6 .x8,
  .logic .and .x .x10 .x10 .x9, .mul .w .x10 .x10 .x16,
  .vop (.dup .s4 .v1 .x10), .vop (.logic .eor .v1 .v1 .v3),
  .vop (.tbl .v2 .v4 .v1), .vop (.logic .eor .v1 .v0 .v5),
  .vop (.logic .and .v1 .v1 .v2), .vop (.logic .eor .v0 .v0 .v1),
  .strq .v0 .x7 0,
  .addImm .x .x5 .x5 16]

/-- Replace the byte of the table at `x0` indexed by `x4` with the byte in
`x14`, returning its original value in `x6`. The two arguments are bytes.
Clobbers `x5`–`x11`, `x16`, and `v0`–`v5`. -/
def replace : Prog isa :=
  .seq (.block replaceSetup) (scanRows replaceStep 16)

/-- Public-index identity-table initialization. -/
def identityStep : List Instr := [
  .add .x .x7 .x0 .x12, .strb .x12 .x7 0,
  .addImm .x .x12 .x12 1, .subImm .x .x11 .x12 256]

def scheduleBefore : List Instr := [
  .add .x .x7 .x0 .x12, .ldrb .x14 .x7 0,
  .add .x .x7 .x17 .x3, .ldrb .x4 .x7 0,
  .add .w .x13 .x13 .x14, .add .w .x13 .x13 .x4,
  .logic .and .x .x13 .x13 .x9, .addImm .x .x4 .x13 0]

def scheduleAfter : Prog isa :=
  .seq (.block [.add .x .x7 .x0 .x12, .strb .x6 .x7 0,
      .addImm .x .x3 .x3 1, .sub .x .x4 .x3 .x1])
    (.seq (.ite (.zero .x .x4) (.block [.movz .x .x3 0 0]) (.block []))
      (.block [.addImm .x .x12 .x12 1, .subImm .x .x11 .x12 256]))

def scheduleStep : Prog isa :=
  .seq (.block scheduleBefore) (.seq replace scheduleAfter)

/-- Key scheduling after the public key-length check succeeds. -/
def initValid : Prog isa :=
  .seq (.block [.addImm .x .x17 .x0 0, .addImm .x .x0 .x2 0,
      .movz .x .x12 0 0, .movz .x .x9 255 0])
    (.seq (.loop (.block identityStep) (.nonzero .x .x11))
      (.seq (.block [.movz .x .x12 0 0, .movz .x .x13 0 0, .movz .x .x3 0 0])
        (.seq (.loop scheduleStep (.nonzero .x .x11))
          (.block [.movz .w .x4 0 0, .strb .x4 .x0 256, .strb .x4 .x0 257,
            .movz .w .x0 0 0]))))

/-- Checked key scheduling; invalid lengths return 1, valid lengths 0. -/
def init : Prog isa :=
  .seq (.block [.subImm .x .x4 .x1 1, .lsr .x .x4 .x4 8])
    (.ite (.nonzero .x .x4) (.block [.movz .w .x0 1 0]) initValid)

def applyBefore : List Instr := [
  .addImm .x .x12 .x12 1, .logic .and .x .x12 .x12 .x9,
  .add .x .x7 .x0 .x12, .ldrb .x14 .x7 0,
  .add .w .x13 .x13 .x14, .logic .and .x .x13 .x13 .x9,
  .addImm .x .x4 .x13 0]

def applyMiddle : List Instr := [
  .add .x .x7 .x0 .x12, .strb .x6 .x7 0,
  .add .w .x4 .x14 .x6, .logic .and .x .x4 .x4 .x9]

def applyAfter : List Instr := [
  .ldrb .x8 .x1 0, .logic .eor .w .x8 .x8 .x6, .strb .x8 .x1 0,
  .addImm .x .x1 .x1 1, .subImm .x .x2 .x2 1]

def applyStep : Prog isa :=
  .seq (.block applyBefore) (.seq replace
    (.seq (.block applyMiddle) (.seq lookup (.block applyAfter))))

/-- Streaming XOR, preserving the permutation and both PRGA indices. -/
def apply : Prog isa :=
  .ite (.zero .x .x2) (.block [])
    (.seq (.block [.ldrb .x12 .x0 256, .ldrb .x13 .x0 257, .movz .x .x9 255 0])
      (.seq (.loop applyStep (.nonzero .x .x2))
        (.block [.strb .x12 .x0 256, .strb .x13 .x0 257])))

end VG.Impl.Rc4.AArch64


