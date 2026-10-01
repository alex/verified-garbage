import VerifiedGarbage.Impl.Sha3.AArch64.Scalar.Core

namespace VG.Impl.Sha3.AArch64.Scalar
open VG VG.AArch64

/-- The two temporary lanes follow the callee-saved GPR prefix. -/
def lowerSpillOffset (k : Nat) : Nat := 96 + 8 * k

/-- Lower the portable operations through the reviewed scalar ISA. v28
backs up x30 around memory accesses; v31 holds the scratch base. -/
def lower : ScalarOp → List Instr
  | .xor d a b => [.logic .eor .x d a b]
  | .xorRor d a b n => [.logicRor .eor .x d a b n]
  | .bic d a b => [.bicRor .x d a b 0]
  | .bicRor d a b n => [.bicRor .x d a b n]
  | .ror d a n => [.ror .x d a n]
  | .move d a => [.addImm .x d a 0]
  | .spill k a =>
    [.vop (.dup .d2 .v28 .x30), .umov .x .x30 .v31 0,
     .str .x a .x30 (lowerSpillOffset k), .umov .x .x30 .v28 0]
  | .reload d k =>
    [.vop (.dup .d2 .v28 .x30), .umov .x .x30 .v31 0,
     .ldr .x d .x30 (lowerSpillOffset k), .umov .x .x30 .v28 0]

def Good : ScalarOp → Prop
  | .xor .. | .bic .. | .move .. => True
  | .xorRor _ _ _ n | .bicRor _ _ _ n => n < 64
  | .ror _ _ n => n < 64
  | .spill k a => k < 2 ∧ a ≠ .x30
  | .reload d k => k < 2 ∧ d ≠ .x30

/-- One round through chi, excluding the round-constant XOR. -/
def coreOps : List ScalarOp := thetaOps ++ rhoPiOps ++ chiOps

def coreInstrs : List Instr := coreOps.flatMap lower

end VG.Impl.Sha3.AArch64.Scalar
