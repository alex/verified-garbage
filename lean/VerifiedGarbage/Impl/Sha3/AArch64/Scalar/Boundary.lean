import VerifiedGarbage.Impl.Sha3.AArch64.Scalar.Core

/-!
# Boundaries for a register-resident scalar Keccak permutation

The 25 state words occupy x0–x24, with the reserved x18 replaced by x25.
Caller-saved v30/v31 retain the two public pointers while all available GPRs
are used by the scalar round. No SHA3 extension is required. Callee-saved
GPRs are retained in caller-saved vectors; no stack frame is
opened, preserving the generic sponge callers' frame contract.
-/

namespace VG.Impl.Sha3.AArch64.Scalar.Boundary

open VG VG.AArch64

abbrev laneReg := VG.Impl.Sha3.AArch64.Scalar.laneReg

def savedReg (i : Nat) : Reg :=
  [Reg.x19,.x20,.x21,.x22,.x23,.x24,.x25,.x26,.x27,.x28,.x30].getD i .x19

/-- Two transient state words occupy scratch[96..112); the round constants
occupy scratch[128..320). The state buffer remains disjoint from scratch. -/
def spillOffset (i : Nat) : Nat := 96 + 8 * i

def savedVec (i : Nat) : VReg :=
  [VReg.v0,.v1,.v2,.v3,.v4,.v5,.v6,.v7,.v16,.v17,.v18].getD i .v0

def save : List Instr :=
  (List.range 11).map (fun i => .vop (.dup .d2 (savedVec i) (savedReg i))) ++
    [.vop (.dup .d2 .v30 .x0),.vop (.dup .d2 .v31 .x1)]

def load : List Instr :=
  [.addImm .x .x30 .x0 0] ++
    (List.range 25).map (fun i => .ldr .x (laneReg i) .x30 (8 * i))

def store : List Instr :=
  [.umov .x .x30 .v30 0] ++
    (List.range 25).map (fun i => .str .x (laneReg i) .x30 (8 * i))

/-- Restore the ABI words from caller-saved vectors without memory traffic. -/
def restore : List Instr :=
  (List.range 11).map (fun i => .umov .x (savedReg i) (savedVec i) 0)

/-- A common ABI boundary around a register-resident scalar permutation core. -/
def wrap (middle : Prog isa) : Prog isa :=
  .seq (.block save) (.seq (.block load)
    (.seq middle (.seq (.block store) (.block restore))))

end VG.Impl.Sha3.AArch64.Scalar.Boundary
