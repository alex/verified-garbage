import VerifiedGarbage.Impl.Sha3.AArch64.Sha3.Vector

namespace VG.Impl.Sha3.AArch64.Sha3.Vector

open VG VG.AArch64

/-- Full q8–q15 saves occupy the first 128 bytes of the existing 512-byte scratch. -/
def saveReg (i : Nat) : List Instr := [.strq (vreg (8 + i)) .x1 (16 * i)]
def save : List Instr := (List.range 8).flatMap saveReg

def loadPair (i : Nat) : List Instr :=
  [.ldrq (vreg (2 * i)) .x0 (16 * i),
    .vop (.ext (vreg (2 * i + 1)) (vreg (2 * i)) (vreg (2 * i)) 8)]
def loadLast : List Instr := [.ldr .x .x17 .x0 192, .vop (.dup .d2 .v24 .x17)]
def load : List Instr := (List.range 12).flatMap loadPair ++ loadLast

def storePair (i : Nat) : List Instr :=
  [.vop (.perm .zip1 .d2 .v25 (vreg (2 * i)) (vreg (2 * i + 1))),
    .strq .v25 .x0 (16 * i)]
def storeLast : List Instr := [.umov .x .x17 .v24 0, .str .x .x17 .x0 192]
def store : List Instr := (List.range 12).flatMap storePair ++ storeLast

def restoreReg (i : Nat) : List Instr := [.ldrq (vreg (8 + i)) .x1 (16 * i)]
def restore : List Instr := (List.range 8).flatMap restoreReg

def permute : Prog isa := .block (save ++ load ++ rounds ++ store ++ restore)

end VG.Impl.Sha3.AArch64.Sha3.Vector
