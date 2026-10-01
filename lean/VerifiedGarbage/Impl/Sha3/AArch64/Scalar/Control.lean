import VerifiedGarbage.Impl.Sha3.AArch64.Scalar.Core

namespace VG.Impl.Sha3.AArch64.Scalar.Control
open VG VG.AArch64

/-- Public FIPS202 constants, with zero high halfwords omitted. -/
def constant (v : BitVec 64) : List Instr :=
  [.movz .x .x26 (v.extractLsb' 0 16) 0] ++
  (if v.extractLsb' 16 16 = 0 then [] else [.movk .x .x26 (v.extractLsb' 16 16) 1]) ++
  (if v.extractLsb' 32 16 = 0 then [] else [.movk .x .x26 (v.extractLsb' 32 16) 2]) ++
  (if v.extractLsb' 48 16 = 0 then [] else [.movk .x .x26 (v.extractLsb' 48 16) 3])

def constantStore (r : Nat) : List Instr :=
  constant (Spec.Sha3.RC r) ++ [.str .x .x26 .x28 (128 + 8 * r)]

/-- Setup runs after the state has been loaded into GPRs. Only scratch GPRs
are used; v31 contains the scratch-buffer pointer saved by the boundary. -/
def setup : List Instr :=
  [.umov .x .x28 .v31 0] ++ (List.range 24).flatMap constantStore ++
  [.addImm .x .x26 .x28 128, .vop (.dup .d2 .v26 .x26),
   .addImm .x .x26 .x28 320, .vop (.dup .d2 .v27 .x26)]

/-- Apply iota and advance the public round-constant pointer. The zero test
uses x27, which is outside the canonical state register mapping. -/
def iotaAdvance : List Instr :=
  [.umov .x .x26 .v26 0, .ldr .x .x27 .x26 0,
   .logic .eor .x .x0 .x0 .x27, .addImm .x .x26 .x26 8,
   .vop (.dup .d2 .v26 .x26), .umov .x .x28 .v27 0,
   .sub .x .x27 .x26 .x28]

def body (core : List Instr) : Prog isa := .block (core ++ iotaAdvance)

def loop (core : List Instr) : Prog isa := .loop (body core) (.nonzero .x .x27)

def middle (core : List Instr) : Prog isa := .seq (.block setup) (loop core)

end VG.Impl.Sha3.AArch64.Scalar.Control
