import VerifiedGarbage.Impl.TripleDes.Arm.Common
import VerifiedGarbage.Impl.TripleDes.Arm.Sbox

namespace VG.Impl.TripleDes.Arm
open VG.Arm
open VG.Spec.TripleDes (Direction)

def savedRegs : List Reg := [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .lr]
def blockSave : List Instr := savedRegs.zipIdx.map fun (r, i) => .str r .r2 (4 * i)
def blockRestore : List Instr := savedRegs.zipIdx.map fun (r, i) => .ldr r .r2 (4 * i)

def blockLoad : List Instr :=
  [.ldr .r4 .r1 0, .ldr .r5 .r1 4, .rev .r4 .r4, .rev .r5 .r5] ++
    permuteCode Spec.TripleDes.ip 64 32 32 .r11 .r10 .r5 .r4 .r12 .r9

def sboxInputs (i : Nat) : List Instr :=
  (List.range 6).flatMap fun j =>
    let k := 6 * i + 5 - j
    let bit := 47 - k
    [.ldr .lr .r0 (if bit < 32 then 0 else 4), rr (q j) .r11] ++
      shr (q j) (32 - Spec.TripleDes.expansion.getD k 1) ++
      [.dp .eor (q j) (q j)
        (if bit % 32 = 0 then .reg .lr else .shifted .lr .lsr (bit % 32)),
        .dp .and (q j) (q j) (.imm 1)]

def sboxOutputs (i : Nat) : List Instr :=
  (List.range 4).flatMap fun j =>
    let position := 4 * i + 4 - j
    let dst := (Spec.TripleDes.p.toList.findIdx? (· == position)).getD 0
    [.dp .and (q j) (q j) (.imm 1)] ++ placeBit (q j) (31 - dst) ++
      [.dp .eor .r10 .r10 (.reg (q j))]

def box (i : Nat) : List Instr := sboxInputs i ++ sboxCode i ++ sboxOutputs i

def swapHalves : List Instr := [rr .lr .r10, rr .r10 .r11, rr .r11 .lr]
def roundBody : List Instr := (List.range 8).flatMap box ++ swapHalves

def roundAdvance (d : Direction) : List Instr :=
  [.dp (if d = .encrypt then .add else .sub) .r0 .r0 (.imm 8), .subs .r9 .r9 (.imm 1)]

/-- Each offset is relative to the pointer left by the preceding pass. -/
def passStart (offset : Int) : List Instr :=
  [.dp (if offset < 0 then .sub else .add) .r0 .r0
    (.imm (BitVec.ofNat 32 offset.natAbs)), imm .r9 16]

def pass (offset : Int) (d : Direction) : Prog isa :=
  .seq (.block (passStart offset))
    (.seq (.loop (.block (roundBody ++ roundAdvance d)) .ne) (.block swapHalves))

def blockBody (d : Direction) : Prog isa :=
  match d with
  | .encrypt => .seq (pass 0 .encrypt) (.seq (pass 120 .decrypt) (pass 136 .encrypt))
  | .decrypt => .seq (pass 376 .decrypt) (.seq (pass (-120) .encrypt) (pass (-136) .decrypt))

def blockStore (d : Direction) : List Instr :=
  permuteCode Spec.TripleDes.fp 64 32 32 .r5 .r4 .r11 .r10 .r12 .r9 ++
    [.rev .r4 .r4, .rev .r5 .r5, .str .r4 .r1 0, .str .r5 .r1 4,
      .dp (if d = .encrypt then .sub else .add) .r0 .r0
        (.imm (if d = .encrypt then 384 else 8))]

def block (d : Direction) : Prog isa :=
  .seq (.block (blockSave ++ blockLoad))
    (.seq (blockBody d) (.block (blockStore d ++ blockRestore)))
def encryptBlock : Prog isa := block .encrypt
def decryptBlock : Prog isa := block .decrypt
end VG.Impl.TripleDes.Arm
