import VerifiedGarbage.Impl.Ed25519.X86_64.PointTable

/-! Public loops generating exact powers of two of a point. -/

namespace VG.Impl.Ed25519.X86_64

open VG.X86_64

def powersNext (count : Nat) : List Instr :=
  [.alu .add .rbx (.imm 1), .movImm64 .rax (BitVec.ofNat 64 count), .alu .cmp .rbx (.reg .rax)]

def powerStride (batch : Bool) : Nat := if batch then 16 else 1

def powerBatch (fld : Arith) (batch : Bool) : Prog isa :=
  if batch then (double16 fld) else .block (pointDouble fld)

/-- Store one power and advance by one or sixteen doublings. -/
def powersBody (fld : Arith) (start count : Nat) (batch : Bool := true) : Prog isa :=
  .seq (.block (tableAddr start ++ pointToTable))
    (.seq (powerBatch fld batch) (.block (powersNext count)))

def pointPowers (fld : Arith) (start count : Nat) (batch : Bool := true) : Prog isa :=
  .seq (.block [.mov32 .rbx (.imm 0)]) (.loop (powersBody fld start count batch) .ne)

end VG.Impl.Ed25519.X86_64
