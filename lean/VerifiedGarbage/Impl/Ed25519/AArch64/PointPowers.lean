import VerifiedGarbage.Impl.Ed25519.AArch64.PointTable

/-! Checkpoints and adjacent powers, using public loop bounds. -/
namespace VG.Impl.Ed25519.AArch64
open VG.AArch64

/-- `x8` = `x19 - count`: nonzero while another power follows. -/
def powersLeft (count : Nat) : List Instr :=
  const64 .x8 (BitVec.ofNat 64 count) ++ [.sub .x .x8 .x19 .x8]

def powersNext (count : Nat) : List Instr := ([.addImm .x .x19 .x19 1] : List Instr) ++ powersLeft count

def powerStride (batch : Bool) : Nat := if batch then 16 else 1

def powerBatch (batch : Bool) : Prog isa :=
  if batch then double16 else .block pointDouble

/-- Store the current power, then advance it only if another power follows:
the last power is not doubled again. -/
def powersBody (start count : Nat) (batch : Bool := true) : Prog isa :=
  .seq (.block (tableAddr start ++ pointToTable ++ powersNext count))
    (.ite (.nonzero .x .x8) (.seq (powerBatch batch) (.block (powersLeft count))) (.block []))

def pointPowers (start count : Nat) (batch : Bool := true) : Prog isa :=
  .seq (.block [.movz .w .x19 0 0])
    (.loop (powersBody start count batch) (.nonzero .x .x8))

end VG.Impl.Ed25519.AArch64
