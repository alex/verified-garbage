import VerifiedGarbage.Impl.TripleDes.X86_64.Common
import VerifiedGarbage.Impl.TripleDes.X86_64.Sbox

/-!
# Scalar Triple DES blocks on x86-64

Two 32-bit Feistel halves stay in `r12` and `r13`. S-box input bits are
formed with fixed shifts and XORs with the round key, passed through Boolean
circuits, and XORed directly into their P-permuted destinations. The three
passes share IP and FP. Round counters and key addresses are public.
Scratch slots 0–5 save callee-saved registers, 6 saves the schedule pointer,
7 holds the round counter, and 8–55 are the S-box's fixed spills.
-/

namespace VG.Impl.TripleDes.X86_64

open VG.X86_64
open VG.Spec.TripleDes (Direction)

def savedRegs : List Reg := [.rbx, .rbp, .r12, .r13, .r14, .r15]

def blockSave : List Instr :=
  (savedRegs.zipIdx.map fun (r, i) => .store (memOp .rdx (8 * i)) r) ++
    [.store (memOp .rdx 48) .rdi]

def blockRestore : List Instr :=
  (savedRegs.zipIdx.map fun (r, i) => .mov r (.mem (memOp .rdx (8 * i)))) ++
    [.mov .rdi (.mem (memOp .rdx 48))]

def blockLoad : List Instr :=
  [.mov .rax (.mem (memOp .rsi 0)), .bswap .rax] ++
    permuteCode Spec.TripleDes.ip 64 .rbx .rax .rbp ++
    [rr .r12 .rbx, .shift .shr .r12 32, .mov32 .r13 (.reg .rbx)]

/-- Six inputs, least significant first, for public S-box number `i`.
The source R bit comes directly from E; the key's upper sixteen bits are
never read as cipher bits. -/
def sboxInputs (i : Nat) : List Instr :=
  [.mov .rbx (.mem (memOp .rdi 0))] ++ (List.range 6).flatMap fun j =>
    let k := 6 * i + 5 - j
    [rr (q j) .r13] ++ shr (q j) (32 - Spec.TripleDes.expansion.getD k 1) ++
      [rr .rbp .rbx] ++ shr .rbp (47 - k) ++
      [.alu .xor (q j) (.reg .rbp), .alu .and (q j) (.imm 1)]

/-- Deposit each output's low bit directly into its destination in L.
The P table contains all 32 positions, so each destination is unique. -/
def sboxOutputs (i : Nat) : List Instr :=
  (List.range 4).flatMap fun j =>
    let position := 4 * i + 4 - j
    let dst := (Spec.TripleDes.p.toList.findIdx? (· == position)).getD 0
    [.alu .and (q j) (.imm 1)] ++ placeBit (q j) (31 - dst) ++
      ([.alu .xor .r12 (.reg (q j))] : List Instr)

def box (i : Nat) : List Instr := sboxInputs i ++ sboxCode i ++ sboxOutputs i

def swapHalves : List Instr := [rr .rax .r12, rr .r12 .r13, rr .r13 .rax]

def roundBody : List Instr := (List.range 8).flatMap box ++ swapHalves

def roundAdvance (direction : Direction) : List Instr :=
  [.alu (if direction = .encrypt then .add else .sub) .rdi (.imm 8),
   .mov .rax (.mem (memOp .rdx 56)), .alu .sub .rax (.imm 1),
   .store (memOp .rdx 56) .rax]

def passStart (component : Nat) (direction : Direction) : List Instr :=
  [.mov .rdi (.mem (memOp .rdx 48)),
   .alu .add .rdi (.imm (BitVec.ofNat 32 (128 * component +
     if direction = .encrypt then 0 else 120))),
   imm .rax 16, .store (memOp .rdx 56) .rax]

def pass (component : Nat) (direction : Direction) : Prog isa :=
  .seq (.block (passStart component direction))
    (.seq (.loop (.block (roundBody ++ roundAdvance direction)) .ne) (.block swapHalves))

def blockStore : List Instr :=
  [rr .rax .r12, .shift .ror .rax 32, .alu .xor .rax (.reg .r13)] ++
    permuteCode Spec.TripleDes.fp 64 .rbx .rax .rbp ++
    [.bswap .rbx, .store (memOp .rsi 0) .rbx]

def blockBody (direction : Direction) : Prog isa :=
  match direction with
  | .encrypt => .seq (pass 0 .encrypt) (.seq (pass 1 .decrypt) (pass 2 .encrypt))
  | .decrypt => .seq (pass 2 .decrypt) (.seq (pass 1 .encrypt) (pass 0 .decrypt))

def block (direction : Direction) : Prog isa :=
  .seq (.block (blockSave ++ blockLoad))
    (.seq (blockBody direction) (.block (blockStore ++ blockRestore)))

def encryptBlock : Prog isa := block .encrypt
def decryptBlock : Prog isa := block .decrypt

end VG.Impl.TripleDes.X86_64
