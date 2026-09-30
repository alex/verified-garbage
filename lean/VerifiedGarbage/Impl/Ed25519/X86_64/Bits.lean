import VerifiedGarbage.Impl.Ed25519.X86_64.PointPowers

/-! Expand a 32- or 64-byte scalar into bits without pruning or clamping. -/

namespace VG.Impl.Ed25519.X86_64

open VG.X86_64

def expandScalarBit (j : Nat) : List Instr :=
  [.mov .rdx (.reg .rax)] ++ (if j = 0 then [] else [.shift .shr .rdx j]) ++
    [.alu .and .rdx (.imm 1), .store8 (VG.Impl.X25519.X86_64.bitAt j) .rdx]

def scalarByteBits (count : Nat) : List Instr :=
  ([.movzx8 .rax { base := .rsi, index := some .rbx }] : List Instr) ++
    (List.range 8).flatMap expandScalarBit ++ powersNext count

def scalarBits (count : Nat) : Prog isa :=
  .seq (.block [.mov32 .rbx (.imm 0)]) (.loop (.block (scalarByteBits count)) .ne)

end VG.Impl.Ed25519.X86_64
