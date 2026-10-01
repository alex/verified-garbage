import VerifiedGarbage.Impl.TripleDes.X86.Common
import VerifiedGarbage.Impl.TripleDes.X86.Sbox

/-! Baseline IA-32 Triple DES. ESI/EDI hold L/R, EBP holds scratch.
Slots 0–3 save callee-saved registers, slot 4 holds the round-key pointer,
slot 5 holds the public round count. All three passes share IP and FP. -/
namespace VG.Impl.TripleDes.X86
open VG.X86
open VG.Spec.TripleDes (Direction)

def savedRegs : List Reg := [.ebp, .ebx, .esi, .edi]
def blockSave : List Instr :=
  [.mov .eax (.mem (memOp .esp 12))] ++
    savedRegs.zipIdx.map (fun (r, i) => .store (memOp .eax (4 * i)) r) ++
    [rr .ebp .eax]
def blockRestore : List Instr :=
  [rr .eax .ebp] ++ savedRegs.zipIdx.map fun (r, i) => .mov r (.mem (memOp .eax (4 * i)))
def blockLoad : List Instr :=
  [.mov .edx (.mem (memOp .esp 8)), .mov .edi (.mem (memOp .edx 0)),
    .mov .esi (.mem (memOp .edx 4)), .bswap .edi, .bswap .esi] ++
    permuteCode Spec.TripleDes.ip 64 32 32 .eax .ebx .esi .edi .ecx ++
    [rr .esi .ebx, rr .edi .eax]

def sboxInputBits (i : Nat) : List Instr :=
  (List.range 6).flatMap fun j =>
    let k := 6 * i + 5 - j
    let bit := 47 - k
    [rr .eax .edi] ++ shr .eax (32 - Spec.TripleDes.expansion.getD k 1) ++
      ([.mov .ecx (.mem (memOp .edx (if bit < 32 then 0 else 4)))] : List Instr) ++
      shr .ecx (if bit < 32 then bit else bit - 32) ++
      [.alu .xor .eax (.reg .ecx), .alu .and .eax (.imm 1),
        .store (memOp .ebp (4 * (16 + j))) .eax]
def sboxInputs (i : Nat) : List Instr :=
  [.mov .edx (.mem (memOp .ebp 16))] ++ sboxInputBits i
def sboxOutputs (i : Nat) : List Instr :=
  (List.range 4).flatMap fun j =>
    let position := 4 * i + 4 - j
    let dst := (Spec.TripleDes.p.toList.findIdx? (· == position)).getD 0
    [.mov .eax (.mem (memOp .ebp (4 * (16 + j)))), .alu .and .eax (.imm 1)] ++
      placeBit .eax (31 - dst) ++ ([.alu .xor .esi (.reg .eax)] : List Instr)
def box (i : Nat) : List Instr := sboxInputs i ++ sboxCode i ++ sboxOutputs i
def swapHalves : List Instr := [rr .eax .esi, rr .esi .edi, rr .edi .eax]
def roundBody : List Instr := (List.range 8).flatMap box ++ swapHalves

def passStart (component : Nat) (direction : Direction) : List Instr :=
  [.mov .eax (.mem (memOp .esp 4)),
    .alu .add .eax (.imm (BitVec.ofNat 32 (128 * component +
      if direction = .encrypt then 0 else 120))),
    .store (memOp .ebp 16) .eax, imm .eax 16, .store (memOp .ebp 20) .eax]
def roundAdvance (direction : Direction) : List Instr :=
  [.mov .eax (.mem (memOp .ebp 16)),
    .alu (if direction = .encrypt then .add else .sub) .eax (.imm 8),
    .store (memOp .ebp 16) .eax, .mov .eax (.mem (memOp .ebp 20)),
    .alu .sub .eax (.imm 1), .store (memOp .ebp 20) .eax]
def pass (component : Nat) (direction : Direction) : Prog isa :=
  .seq (.block (passStart component direction))
    (.seq (.loop (.block (roundBody ++ roundAdvance direction)) .ne) (.block swapHalves))
def blockBody (direction : Direction) : Prog isa :=
  match direction with
  | .encrypt => .seq (pass 0 .encrypt) (.seq (pass 1 .decrypt) (pass 2 .encrypt))
  | .decrypt => .seq (pass 2 .decrypt) (.seq (pass 1 .encrypt) (pass 0 .decrypt))
def blockStore : List Instr :=
  permuteCode Spec.TripleDes.fp 64 32 32 .eax .ebx .edi .esi .ecx ++
    [.bswap .ebx, .bswap .eax, .mov .edx (.mem (memOp .esp 8)),
      .store (memOp .edx 0) .ebx, .store (memOp .edx 4) .eax]
def block (direction : Direction) : Prog isa :=
  .seq (.block (blockSave ++ blockLoad))
    (.seq (blockBody direction) (.block (blockStore ++ blockRestore)))
def encryptBlock : Prog isa := block .encrypt
def decryptBlock : Prog isa := block .decrypt
end VG.Impl.TripleDes.X86
