import VerifiedGarbage.Impl.Rc2.AArch64.Lookup

/-! # RC2 block encryption and decryption on baseline AArch64 -/

namespace VG.Impl.Rc2.AArch64

open VG.AArch64

def wordReg (i : Nat) : Reg := #[Reg.x19, .x20, .x21, .x22][i % 4]!

def blockSave : List Instr :=
  (List.range 4).map fun i => .str .x (wordReg i) .x2 (8 * i)

def blockRestore : List Instr :=
  (List.range 4).map fun i => .ldr .x (wordReg i) .x2 (8 * i)

def unpackWord (i : Nat) : List Instr :=
  [rr (wordReg i) .x8, .lsr .x (wordReg i) (wordReg i) (16 * i)] ++
    mask (wordReg i) 16

def blockLoad : List Instr :=
  [.ldr .x .x8 .x1 0] ++ (List.range 4).flatMap unpackWord

def rotate16 (r : Reg) (s : Nat) : List Instr :=
  [rr .x8 r, .lsr .x .x8 .x8 (16 - s), .ror .x r r (64 - s),
   .logic .orr .x r r .x8] ++ mask r 16

def mixInputs (j i : Nat) : List Instr :=
  [.logic .and .x .x6 (wordReg (i + 3)) (wordReg (i + 2)),
   imm .x7 0, .sub .x .x7 .x7 (wordReg (i + 3)), .subImm .x .x7 .x7 1,
   .logic .and .x .x7 .x7 (wordReg (i + 1)), .add .x .x6 .x6 .x7] ++ loadKey j

def addInputs (r : Reg) : List Instr :=
  [.add .x r r .x4, .add .x r r .x6] ++ mask r 16

def subInputs (r : Reg) : List Instr :=
  [.sub .x r r .x4, .sub .x r r .x6] ++ mask r 16

def adjust (sub : Bool) (r : Reg) : List Instr :=
  [if sub then .sub .x r r .x8 else .add .x r r .x8] ++ mask r 16

def mix (j i : Nat) : List Instr :=
  mixInputs j i ++ addInputs (wordReg i) ++ rotate16 (wordReg i) (Spec.Rc2.rotation i)

def reverseMix (j i : Nat) : List Instr :=
  rotate16 (wordReg i) (16 - Spec.Rc2.rotation i) ++ mixInputs j i ++ subInputs (wordReg i)

def mash (direction : Spec.Rc2.Direction) (i : Nat) : List Instr :=
  [rr .x8 (wordReg (i + 3))] ++ keyLookup ++ adjust (direction == .decrypt) (wordReg i)

def round (direction : Spec.Rc2.Direction) (j : Nat) : List Instr :=
  match direction with
  | .encrypt => (List.range 4).flatMap (fun i => mix (4 * j + i) i) ++
      (if j = 4 ∨ j = 10 then (List.range 4).flatMap (mash .encrypt) else [])
  | .decrypt => [3, 2, 1, 0].flatMap (fun i => reverseMix (4 * (15 - j) + i) i) ++
      (if j = 4 ∨ j = 10 then [3, 2, 1, 0].flatMap (mash .decrypt) else [])

def packWord (i : Nat) : List Instr :=
  [.ror .x .x3 (wordReg i) (64 - 16 * i), .logic .orr .x .x8 .x8 .x3]

def blockStore : List Instr :=
  [rr .x8 (wordReg 0)] ++ [1, 2, 3].flatMap packWord ++ [.str .x .x8 .x1 0]

def blockCode (direction : Spec.Rc2.Direction) : List Instr :=
  blockSave ++ blockLoad ++ (List.range 16).flatMap (round direction) ++ blockStore ++ blockRestore

def encryptBlock : Prog isa := .block (blockCode .encrypt)
def decryptBlock : Prog isa := .block (blockCode .decrypt)

end VG.Impl.Rc2.AArch64
