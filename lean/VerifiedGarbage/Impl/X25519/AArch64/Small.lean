import VerifiedGarbage.Impl.Ed25519.AArch64.Word

/-! Multiplication by X25519's ladder constant, using one wide product row. -/
namespace VG.Impl.X25519.AArch64
open VG.AArch64 VG.Impl.Ed25519.AArch64

def mulA24 (o a : Nat) : List Instr :=
  [.movz .w .x10 0 0] ++ const64 .x3 121665 ++ loads a .x12 .x13 .x14 .x15 ++
  rowFirst .x3 .x12 .x13 .x14 .x15 .x4 .x5 .x6 .x7 .x21 ++
  [VG.Impl.Ed25519.AArch64.mov .x20 .x21, .movz .w .x11 38 0] ++ fold ++ store4 o
end VG.Impl.X25519.AArch64
