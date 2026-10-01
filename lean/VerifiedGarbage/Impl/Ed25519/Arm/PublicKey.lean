import VerifiedGarbage.TCB.Arm.Isa

namespace VG.Impl.Ed25519.Arm.PublicKey
open VG.Arm

def pruneLow : List Instr :=
  [.movw .r1 0xfff8, .movt .r1 0xffff, .dp .and .r0 .r0 (.reg .r1)]
def pruneHigh : List Instr :=
  [.movw .r1 0xffff, .movt .r1 0x3fff, .dp .and .r0 .r0 (.reg .r1),
    .movw .r1 0, .movt .r1 0x4000, .dp .orr .r0 .r0 (.reg .r1)]
def pruneWord (k : Nat) : List Instr :=
  [.ldrSp .r0 (184 + 4 * k)] ++ (if k = 0 then pruneLow else if k = 7 then pruneHigh else []) ++
    [.addSp .r12 24, .str .r0 .r12 (4 * k)]
def prune : List Instr := (List.range 8).flatMap pruneWord

end VG.Impl.Ed25519.Arm.PublicKey
