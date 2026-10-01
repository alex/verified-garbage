import VerifiedGarbage.Impl.Ed25519.AArch64.ScalarBase
import VerifiedGarbage.Impl.Sha512.AArch64.Stream
import VerifiedGarbage.Spec.Sha512.Contract

namespace VG.Impl.Ed25519.AArch64.PublicKey
open VG.AArch64

/-- Clear the low three bits of the first digest word. -/
def pruneLow : List Instr :=
  [.movz .x .x10 0xfff8 0, .movk .x .x10 0xffff 1, .movk .x .x10 0xffff 2,
    .movk .x .x10 0xffff 3, .logic .and .x .x9 .x9 .x10]

/-- Clear bit 255 and set bit 254 in the fourth digest word. -/
def pruneHigh : List Instr :=
  [.movz .x .x10 0xffff 0, .movk .x .x10 0xffff 1, .movk .x .x10 0xffff 2,
    .movk .x .x10 0x3fff 3, .logic .and .x .x9 .x9 .x10,
    .movz .x .x10 0x4000 3, .logic .orr .x .x9 .x9 .x10]

/-- Copy and prune word `k` from the seed digest to the scalar. -/
def pruneWord (k : Nat) : List Instr :=
  [.ldrSp .x9 (192 + 8 * k)] ++
    (if k = 0 then pruneLow else if k = 3 then pruneHigh else []) ++
    [.addSp .x15 (32 + 8 * k), .str .x .x9 .x15 0]

def prunePrefix (n : Nat) : List Instr := (List.range n).flatMap pruneWord

def prune : List Instr := prunePrefix 4

end VG.Impl.Ed25519.AArch64.PublicKey
