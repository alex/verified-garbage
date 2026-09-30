import VerifiedGarbage.Impl.Ed25519.AArch64.PointLoop

/-! Points in bounded tables; x8 is the current public entry pointer. -/
namespace VG.Impl.Ed25519.AArch64
open VG.AArch64

def tableWords (dst : Nat) : List Instr :=
  [.str .x .x4 .x8 dst, .str .x .x5 .x8 (dst + 8),
    .str .x .x6 .x8 (dst + 16), .str .x .x7 .x8 (dst + 24)]

def fromTableWords (src : Nat) : List Instr :=
  [.ldr .x .x4 .x8 src, .ldr .x .x5 .x8 (src + 8),
    .ldr .x .x6 .x8 (src + 16), .ldr .x .x7 .x8 (src + 24)]

def pointToTable : List Instr :=
  (List.range 4).flatMap fun j =>
    loads (64 + 32 * j) .x4 .x5 .x6 .x7 ++ tableWords (32 * j)

def pointFromTable : List Instr :=
  (List.range 4).flatMap fun j =>
    fromTableWords (32 * j) ++ stores (64 + 32 * j) .x4 .x5 .x6 .x7

def tableAddr (off : Nat) : List Instr :=
  [.lsl .x .x8 .x19 7, .add .x .x8 .x8 .x0] ++ const64 .x3 (BitVec.ofNat 64 off) ++
    [.add .x .x8 .x8 .x3]

end VG.Impl.Ed25519.AArch64
