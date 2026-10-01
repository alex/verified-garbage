import VerifiedGarbage.Impl.Sha3.AArch64.Scalar.Core

namespace VG.Impl.Sha3.AArch64.Scalar
open VG VG.AArch64

/-- Caller-saved vectors retain the two temporary lanes. -/
def tempSlotV (k : Nat) : VReg := if k = 0 then .v24 else .v25

/-- Lower portable operations through the reviewed scalar ISA. Temporary
lanes remain in vectors; no round-stage scratch-memory traffic is needed. -/
def lower : ScalarOp → List Instr
  | .xor d a b => [.logic .eor .x d a b]
  | .xorRor d a b n => [.logicRor .eor .x d a b n]
  | .bic d a b => [.bicRor .x d a b 0]
  | .bicRor d a b n => [.bicRor .x d a b n]
  | .ror d a n => [.ror .x d a n]
  | .move d a => [.addImm .x d a 0]
  | .spill k a => [.vop (.dup .d2 (tempSlotV k) a)]
  | .reload d k => [.umov .x d (tempSlotV k) 0]

def Good : ScalarOp → Prop
  | .xor .. | .bic .. | .move .. => True
  | .xorRor _ _ _ n | .bicRor _ _ _ n => n < 64
  | .ror _ _ n => n < 64
  | .spill k a => k < 2 ∧ a ≠ .x30
  | .reload d k => k < 2 ∧ d ≠ .x30

/-- One round through chi, excluding the round-constant XOR. -/
def coreOps : List ScalarOp := thetaOps ++ rhoPiOps ++ chiOps

end VG.Impl.Sha3.AArch64.Scalar
