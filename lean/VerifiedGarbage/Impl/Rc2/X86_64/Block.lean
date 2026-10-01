import VerifiedGarbage.Impl.Rc2.X86_64.Sse2KeyLookup

/-! # RC2 block encryption and decryption on baseline x86-64 -/

namespace VG.Impl.Rc2.X86_64

open VG.X86_64

/-- Four 16-bit state words, zero-extended in callee-saved registers. -/
def wordReg (i : Nat) : Reg := #[Reg.r12, .r13, .r14, .r15][i % 4]!

def blockSave : List Instr :=
  (List.range 4).map fun i => .store (memOp .rdx (8 * i)) (wordReg i)

def blockRestore : List Instr :=
  (List.range 4).map fun i => .mov (wordReg i) (.mem (memOp .rdx (8 * i)))

def unpackWord (i : Nat) : List Instr :=
  [rr (wordReg i) .rax] ++
    (if i = 0 then [] else [.shift .shr (wordReg i) (16 * i)]) ++
    [.alu .and (wordReg i) (.imm 65535)]

def blockLoad : List Instr :=
  [.mov .rax (.mem (memOp .rsi 0))] ++ (List.range 4).flatMap unpackWord

/-- Rotate a zero-extended 16-bit word left by `s` (1–15), with `rax` as
temporary. A 64-bit rotate implements the left shift because the input's
upper 48 bits are zero. -/
def rotate16 (r : Reg) (s : Nat) : List Instr :=
  [rr .rax r, .shift .shr .rax (16 - s), .shift .ror r (64 - s),
   .alu .or r (.reg .rax), .alu .and r (.imm 65535)]

/-- The composite word in `r10`, and round key word `j` in `r8`. -/
def mixInputs (j i : Nat) : List Instr :=
  [rr .r10 (wordReg (i + 3)), .alu .and .r10 (.reg (wordReg (i + 2))),
   rr .r11 (wordReg (i + 3)), .alu .xor .r11 (.imm (-1)),
   .alu .and .r11 (.reg (wordReg (i + 1))), .alu .add .r10 (.reg .r11)] ++ loadKey j

def mix (j i : Nat) : List Instr :=
  mixInputs j i ++
    ([.alu .add (wordReg i) (.reg .r8), .alu .add (wordReg i) (.reg .r10),
      .alu .and (wordReg i) (.imm 65535)] : List Instr) ++
    rotate16 (wordReg i) (Spec.Rc2.rotation i)

def reverseMix (j i : Nat) : List Instr :=
  rotate16 (wordReg i) (16 - Spec.Rc2.rotation i) ++ mixInputs j i ++
    [.alu .sub (wordReg i) (.reg .r8), .alu .sub (wordReg i) (.reg .r10),
     .alu .and (wordReg i) (.imm 65535)]

def mash (direction : Spec.Rc2.Direction) (i : Nat) : List Instr :=
  [rr .rax (wordReg (i + 3))] ++ Sse2.keyLookup ++
    [.alu (if direction = .encrypt then .add else .sub) (wordReg i) (.reg .rax),
     .alu .and (wordReg i) (.imm 65535)]

def round (direction : Spec.Rc2.Direction) (j : Nat) : List Instr :=
  match direction with
  | .encrypt => (List.range 4).flatMap (fun i => mix (4 * j + i) i) ++
      (if j = 4 ∨ j = 10 then (List.range 4).flatMap (mash .encrypt) else [])
  | .decrypt => [3, 2, 1, 0].flatMap (fun i => reverseMix (4 * (15 - j) + i) i) ++
      (if j = 4 ∨ j = 10 then [3, 2, 1, 0].flatMap (mash .decrypt) else [])

def packWord (i : Nat) : List Instr :=
  [rr .rcx (wordReg i), .shift .ror .rcx (64 - 16 * i), .alu .or .rax (.reg .rcx)]

def blockStore : List Instr :=
  [rr .rax (wordReg 0)] ++ [1, 2, 3].flatMap packWord ++ [.store (memOp .rsi 0) .rax]

def blockCode (direction : Spec.Rc2.Direction) : List Instr :=
  blockSave ++ blockLoad ++ (List.range 16).flatMap (round direction) ++ blockStore ++ blockRestore

def encryptBlock : Prog isa := .block (blockCode .encrypt)
def decryptBlock : Prog isa := .block (blockCode .decrypt)

end VG.Impl.Rc2.X86_64
