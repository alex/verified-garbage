import VerifiedGarbage.Impl.Rc2.X86.ExpandKey

/-! # RC2 block rounds on baseline x86

The four words live at scratch offsets 64..79. Each MIX loads the words into
EAX..EDX and writes back one result. EBP stays pinned to scratch; the schedule
pointer is read from the original stack argument. MASH scans all 64 schedule
words, so its addresses and branches never depend on secret data.
-/

namespace VG.Impl.Rc2.X86

open VG.X86

/-- ECX is also preserved so CBC can keep its IV pointer across calls. -/
def blockSaved : List Reg := [.ebp, .ebx, .esi, .edi, .ecx]

def blockSave : List Instr :=
  blockSaved.zipIdx |>.map fun (r, i) => .store (memOp .eax (4 * i)) r

def blockRestore : List Instr :=
  blockSaved.zipIdx |>.map fun (r, i) => .mov r (.mem (memOp .eax (4 * i)))

def wordReg (i : Nat) : Reg := #[Reg.eax, .ebx, .ecx, .edx][i % 4]!

def wordOff (i : Nat) : Nat := 64 + 4 * (i % 4)

def loadWords : List Instr :=
  (List.range 4).map fun i => .mov (wordReg i) (.mem (memOp .ebp (wordOff i)))

def rotate16 (r : Reg) (n : Nat) : List Instr :=
  [rr .esi r, .shift .shr .esi (16 - n), .shift .ror r (32 - n),
    .alu .or r (.reg .esi), .alu .and r (.imm 65535)]

def mixSelect (i : Nat) : List Instr :=
  [rr .esi (wordReg (i + 2)), .alu .xor .esi (.reg (wordReg (i + 1))),
    .alu .and .esi (.reg (wordReg (i + 3))), .alu .xor .esi (.reg (wordReg (i + 1)))]

def mixKey (j : Nat) : List Instr :=
  [.mov .edi (.mem (memOp .esp 4)), .movzx8 .esi (memOp .edi (2 * j)),
    .movzx8 .edi (memOp .edi (2 * j + 1)), .shift .ror .edi 24, .alu .or .esi (.reg .edi)]

def adjust (sub : Bool) (r : Reg) : List Instr :=
  [if sub then .alu .sub r (.reg .esi) else .alu .add r (.reg .esi)]

def mixArithmetic (sub : Bool) (j i : Nat) : List Instr :=
  mixSelect i ++ adjust sub (wordReg i) ++ mixKey j ++ adjust sub (wordReg i) ++
    [.alu .and (wordReg i) (.imm 65535)]

def mixCore (d : Spec.Rc2.Direction) (j i : Nat) : List Instr :=
  match d with
  | .encrypt => mixArithmetic false j i ++ rotate16 (wordReg i) (Spec.Rc2.rotation i)
  | .decrypt => rotate16 (wordReg i) (16 - Spec.Rc2.rotation i) ++ mixArithmetic true j i

def mix (j i : Nat) : List Instr :=
  loadWords ++ mixCore .encrypt j i ++ [.store (memOp .ebp (wordOff i)) (wordReg i)]

def reverseMix (j i : Nat) : List Instr :=
  loadWords ++ mixCore .decrypt j i ++ [.store (memOp .ebp (wordOff i)) (wordReg i)]

def mashInput (i : Nat) : List Instr :=
  [.mov .eax (.mem (memOp .ebp (wordOff (i + 3)))), .mov .edi (.mem (memOp .esp 4))]

def mashAdjust (direction : Spec.Rc2.Direction) (i : Nat) : List Instr :=
  [.mov .edx (.mem (memOp .ebp (wordOff i))),
    if direction == .decrypt then .alu .sub .edx (.reg .eax) else .alu .add .edx (.reg .eax),
    .alu .and .edx (.imm 65535)]

def mash (direction : Spec.Rc2.Direction) (i : Nat) : List Instr :=
  mashInput i ++ keyLookup ++ mashAdjust direction i ++ [.store (memOp .ebp (wordOff i)) .edx]

def round (direction : Spec.Rc2.Direction) (j : Nat) : List Instr :=
  match direction with
  | .encrypt => (List.range 4).flatMap (fun i => mix (4 * j + i) i) ++
      (if j = 4 ∨ j = 10 then (List.range 4).flatMap (mash .encrypt) else [])
  | .decrypt => [3, 2, 1, 0].flatMap (fun i => reverseMix (4 * (15 - j) + i) i) ++
      (if j = 4 ∨ j = 10 then [3, 2, 1, 0].flatMap (mash .decrypt) else [])

def loadWord (i : Nat) : List Instr :=
  [.movzx8 .eax (memOp .edi (2 * i)), .movzx8 .edx (memOp .edi (2 * i + 1)),
    .shift .ror .edx 24, .alu .or .eax (.reg .edx), .store (memOp .ebp (wordOff i)) .eax]

def storeWord (i : Nat) : List Instr :=
  [.mov .eax (.mem (memOp .ebp (wordOff i))), .store8 (memOp .edi (2 * i)) .al,
    .shift .shr .eax 8, .store8 (memOp .edi (2 * i + 1)) .al]

def blockCode (direction : Spec.Rc2.Direction) : List Instr :=
  ([.mov .eax (.mem (memOp .esp 12))] : List Instr) ++ blockSave ++
    ([rr .ebp .eax, .mov .edi (.mem (memOp .esp 8))] : List Instr) ++
    (List.range 4).flatMap loadWord ++ (List.range 16).flatMap (round direction) ++
    ([.mov .edi (.mem (memOp .esp 8))] : List Instr) ++ (List.range 4).flatMap storeWord ++
    ([rr .eax .ebp] : List Instr) ++ blockRestore

def encryptBlock : Prog isa := .block (blockCode .encrypt)
def decryptBlock : Prog isa := .block (blockCode .decrypt)

end VG.Impl.Rc2.X86
