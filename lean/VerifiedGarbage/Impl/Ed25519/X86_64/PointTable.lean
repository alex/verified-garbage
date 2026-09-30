import VerifiedGarbage.Impl.Ed25519.X86_64.PointLoop

/-! Moving points between the arithmetic workspace and bounded tables. -/

namespace VG.Impl.Ed25519.X86_64

open VG.X86_64
open VG.Impl.X25519.X86_64 (at_ loads stores)

def tableWords (dst : Nat) : List Instr :=
  [.store (at_ .rax dst) .r8, .store (at_ .rax (dst + 8)) .r9,
    .store (at_ .rax (dst + 16)) .r10, .store (at_ .rax (dst + 24)) .r11]

def fromTableWords (src : Nat) : List Instr :=
  [.mov .r8 (.mem (at_ .rax src)), .mov .r9 (.mem (at_ .rax (src + 8))),
    .mov .r10 (.mem (at_ .rax (src + 16))), .mov .r11 (.mem (at_ .rax (src + 24)))]

/-- The current point to a table entry addressed by the public rax pointer. -/
def pointToTable : List Instr :=
  (List.range 4).flatMap fun j =>
    loads (64 + 32 * j) .r8 .r9 .r10 .r11 ++ tableWords (32 * j)

/-- A table entry to the first point in the arithmetic workspace. -/
def pointFromTable : List Instr :=
  (List.range 4).flatMap fun j =>
    fromTableWords (32 * j) ++ stores (64 + 32 * j) .r8 .r9 .r10 .r11

/-- The j-th 128-byte point, for j in rbx, in the table beginning at off. -/
def tableAddr (off : Nat) : List Instr :=
  [.mov .rax (.reg .rbx), .movImm64 .rcx 128, .mul .rcx, .alu .add .rax (.reg .rdi),
    .movImm64 .rcx (BitVec.ofNat 64 off), .alu .add .rax (.reg .rcx)]

end VG.Impl.Ed25519.X86_64
