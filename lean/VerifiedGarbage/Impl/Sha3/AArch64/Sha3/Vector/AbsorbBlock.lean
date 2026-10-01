import VerifiedGarbage.Impl.Sha3.AArch64.Sha3.Vector

namespace VG.Impl.Sha3.AArch64.Sha3.Vector

open VG VG.AArch64

/-- XOR two input words at x3+16*i into canonical state lanes. -/
def absorbPair (i : Nat) : List Instr :=
  [.ldrq .v25 .x3 (16*i), .vop (.ext .v26 .v25 .v25 8),
    .vop (.logic .eor (vreg (2*i)) (vreg (2*i)) .v25),
    .vop (.logic .eor (vreg (2*i+1)) (vreg (2*i+1)) .v26)]

/-- The final word of an odd-word rate. -/
def absorbWord (i : Nat) : List Instr :=
  [.ldr .x .x17 .x3 (8*i), .vop (.dup .d2 .v25 .x17),
    .vop (.logic .eor (vreg i) (vreg i) .v25)]

def absorbWords (n : Nat) : List Instr :=
  (List.range (n/2)).flatMap absorbPair ++ (if n%2=1 then absorbWord (n-1) else [])

/-- Compile-time rate, input pointer x3 unchanged; only x17 and vectors change.
The state remains in v0–v24 and memory is untouched. -/
def absorbBlock (rate : Nat) : List Instr := absorbWords (rate/8)

end VG.Impl.Sha3.AArch64.Sha3.Vector
