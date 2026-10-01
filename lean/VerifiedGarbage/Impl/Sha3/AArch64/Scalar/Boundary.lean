import VerifiedGarbage.Impl.Sha3.AArch64.Scalar.Core

/-!
# Boundaries for a register-resident scalar Keccak permutation

The 25 state words occupy x0–x24, with the reserved x18 replaced by x25.
Caller-saved v30/v31 retain the two public pointers while all available GPRs
are used by the scalar round. No SHA3 extension is required. Callee-saved
GPRs are saved in the existing 512-byte scratch region; no stack frame is
opened, preserving the generic sponge callers' frame contract.
-/

namespace VG.Impl.Sha3.AArch64.Scalar.Boundary

open VG VG.AArch64

abbrev laneReg := VG.Impl.Sha3.AArch64.Scalar.laneReg

def savedReg (i : Nat) : Reg :=
  [Reg.x19,.x20,.x21,.x22,.x23,.x24,.x25,.x26,.x27,.x28,.x30].getD i .x19

/-- The existing scratch contains saved GPRs in [0,88) and two transient
state words in [96,112). The state buffer remains disjoint from scratch. -/
def spillOffset (i : Nat) : Nat := 96 + 8 * i

def save : List Instr :=
  (List.range 11).map (fun i => .str .x (savedReg i) .x1 (8 * i)) ++
    [.vop (.dup .d2 .v30 .x0),.vop (.dup .d2 .v31 .x1)]

def load : List Instr :=
  [.addImm .x .x30 .x0 0] ++
    (List.range 25).map (fun i => .ldr .x (laneReg i) .x30 (8 * i))

def store : List Instr :=
  [.umov .x .x30 .v30 0] ++
    (List.range 25).map (fun i => .str .x (laneReg i) .x30 (8 * i))

/-- x17 is free after the state has been stored; restoring x30 last preserves
both the saved return register and the scratch base for every load. -/
def restore : List Instr :=
  [.umov .x .x17 .v31 0] ++
    (List.range 11).map (fun i => .ldr .x (savedReg i) .x17 (8 * i))

/-- A common ABI boundary around a register-resident scalar permutation core. -/
def wrap (middle : Prog isa) : Prog isa :=
  .seq (.block save) (.seq (.block load)
    (.seq middle (.seq (.block store) (.block restore))))

end VG.Impl.Sha3.AArch64.Scalar.Boundary
