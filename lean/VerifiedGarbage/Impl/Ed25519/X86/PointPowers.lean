import VerifiedGarbage.Impl.Ed25519.X86.PointTable
import VerifiedGarbage.Impl.Ed25519.X86.PointLoop

/-! Checkpoint tables and local batches share a public counter at byte24. -/
namespace VG.Impl.Ed25519.X86
open VG.X86
open VG.Impl.X25519.X86 (sc)

def powerStride (batch : Bool) : Nat := if batch then 16 else 1
def powerBatch (batch : Bool) : Prog isa :=
  if batch then double16 else .block pointDouble

def powersNext (count : Nat) : List Instr :=
  [.mov .esi (.mem (sc 24)), .alu .add .esi (.imm 1), .store (sc 24) .esi,
    .alu .cmp .esi (.imm (BitVec.ofNat 32 count))]

def powersBody (start count : Nat) (batch : Bool := true) : Prog isa :=
  .seq (.block [.mov .esi (.mem (sc 24))])
    (.seq (.block (tableAddr start ++ pointToTable))
      (.seq (powerBatch batch) (.block (powersNext count))))

def pointPowers (start count : Nat) (batch : Bool := true) : Prog isa :=
  .seq (.block [.mov .eax (.imm 0), .store (sc 24) .eax])
    (.loop (powersBody start count batch) .ne)

end VG.Impl.Ed25519.X86
