import VerifiedGarbage.Impl.Ed25519.X86_64.PointTable

/-! Public loops generating exact powers of two of a point. -/

namespace VG.Impl.Ed25519.X86_64

open VG.X86_64

def powersNext (count : Nat) : List Instr :=
  [.alu .add .rbx (.imm 1), .movImm64 .rax (BitVec.ofNat 64 count), .alu .cmp .rbx (.reg .rax)]

/-- Store one checkpoint and advance the point by sixteen doublings. -/
def powersBody (start count : Nat) : Prog isa :=
  .seq (.block (tableAddr start ++ pointToTable))
    (.seq double16 (.block (powersNext count)))

def pointPowers (start count : Nat) : Prog isa :=
  .seq (.block [.mov32 .rbx (.imm 0)]) (.loop (powersBody start count) .ne)

end VG.Impl.Ed25519.X86_64
