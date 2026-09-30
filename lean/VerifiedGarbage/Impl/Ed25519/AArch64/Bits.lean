import VerifiedGarbage.Impl.Ed25519.AArch64.PointPowers

/-! Expand 32 or 64 scalar bytes into bit bytes, without pruning. -/
namespace VG.Impl.Ed25519.AArch64
open VG.AArch64

def expandScalarBit (j : Nat) : List Instr :=
  [.lsr .x .x2 .x8 j, .logic .and .x .x2 .x2 .x11, .strb .x2 .x9 (768 + j)]

def scalarByteBits (count : Nat) : List Instr :=
  ([.add .x .x8 .x1 .x19, .ldrb .x8 .x8 0,
    .lsl .x .x9 .x19 3, .add .x .x9 .x0 .x9] : List Instr) ++
    (List.range 8).flatMap expandScalarBit ++ powersNext count

def scalarBits (count : Nat) : Prog isa :=
  .seq (.block [.movz .w .x19 0 0, .movz .w .x11 1 0])
    (.loop (.block (scalarByteBits count)) (.nonzero .x .x8))

end VG.Impl.Ed25519.AArch64
