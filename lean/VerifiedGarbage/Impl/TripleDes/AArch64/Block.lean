import VerifiedGarbage.Impl.TripleDes.AArch64.Common
import VerifiedGarbage.Impl.TripleDes.AArch64.Sbox

namespace VG.Impl.TripleDes.AArch64

open VG.AArch64
open VG.Spec.TripleDes (Direction)

def savedRegs : List Reg := [.x19, .x20, .x21, .x22]

def blockSave : List Instr := savedRegs.zipIdx.map fun (r, i) => .str .x r .x2 (8 * i)
def blockRestore : List Instr := savedRegs.zipIdx.map fun (r, i) => .ldr .x r .x2 (8 * i)

def blockLoad : List Instr :=
  [.ldr .x .x3 .x1 0, .rev .x3 .x3] ++
    permuteCode Spec.TripleDes.ip 64 .x10 .x3 .x11 .x12 ++
    [.lsr .x .x19 .x10 32, rr .x20 .x10] ++ mask .x20 32

def sboxInputs (i : Nat) : List Instr :=
  [.ldr .x .x10 .x22 0, imm .x12 1] ++ (List.range 6).flatMap fun j =>
    let k := 6 * i + 5 - j
    [rr (q j) .x20] ++ shr (q j) (32 - Spec.TripleDes.expansion.getD k 1) ++
      [rr .x11 .x10] ++ shr .x11 (47 - k) ++
      [.logic .eor .x (q j) (q j) .x11, .logic .and .x (q j) (q j) .x12]

def sboxOutputs (i : Nat) : List Instr :=
  [imm .x10 1] ++ (List.range 4).flatMap fun j =>
    let position := 4 * i + 4 - j
    let dst := (Spec.TripleDes.p.toList.findIdx? (· == position)).getD 0
    [.logic .and .x (q j) (q j) .x10] ++ placeBit (q j) (31 - dst) ++
      [.logic .eor .x .x19 .x19 (q j)]

def box (i : Nat) : List Instr := sboxInputs i ++ sboxCode i ++ sboxOutputs i

def swapHalves : List Instr := [rr .x3 .x19, rr .x19 .x20, rr .x20 .x3]

def roundBody : List Instr := (List.range 8).flatMap box ++ swapHalves

def roundAdvance (d : Direction) : List Instr :=
  [if d = .encrypt then .addImm .x .x22 .x22 8 else .subImm .x .x22 .x22 8,
    .subImm .x .x21 .x21 1]

def passStart (component : Nat) (d : Direction) : List Instr :=
  [.addImm .x .x22 .x0 (128 * component + if d = .encrypt then 0 else 120),
    imm .x21 16]

def pass (component : Nat) (d : Direction) : Prog isa :=
  .seq (.block (passStart component d))
    (.seq (.loop (.block (roundBody ++ roundAdvance d)) (.nonzero .x .x21)) (.block swapHalves))

def blockBody (d : Direction) : Prog isa :=
  match d with
  | .encrypt => .seq (pass 0 .encrypt) (.seq (pass 1 .decrypt) (pass 2 .encrypt))
  | .decrypt => .seq (pass 2 .decrypt) (.seq (pass 1 .encrypt) (pass 0 .decrypt))

def blockStore : List Instr :=
  [.lsl .x .x3 .x19 32, .logic .eor .x .x3 .x3 .x20] ++
    permuteCode Spec.TripleDes.fp 64 .x10 .x3 .x11 .x12 ++ [.rev .x3 .x10]

def block (d : Direction) : Prog isa :=
  .seq (.block (blockSave ++ blockLoad))
    (.seq (blockBody d) (.block (blockStore ++ blockRestore ++ [.str .x .x3 .x1 0])))

def encryptBlock : Prog isa := block .encrypt
def decryptBlock : Prog isa := block .decrypt

end VG.Impl.TripleDes.AArch64
