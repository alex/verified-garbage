import VerifiedGarbage.TCB.X86_64.Isa

/-!
# RC4 on baseline x86-64

The 256-byte table at `rdi` is 32 quadwords. A secret-indexed lookup visits
every quadword at its fixed address, keeping the one that holds the byte
with a mask, then every byte of that quadword. A secret-indexed
replacement visits every quadword again and stores it back, XORed with a
masked difference that is nonzero only in the selected byte. Masks come
from `sub` and `sbb`: subtracting a bound borrows exactly when the masked
candidate matches. Only the quadword addresses, the PRGA index `i`, the
key offset and the pointers are public.

Registers: the table at `rdi`, the public index `i` in `rcx`, the secret
index of a lookup or replacement in `r9`, its result in `rax`; `r10` and
`r11` are scratch. Initialization keeps the key at `rsi`, its length in
`rdx`, the key offset in `r8` and `j` in `r9`; the stream function keeps
the data at `rsi`, the remaining length in `rdx` and `j` in `r8`. Only
caller-saved registers are used, and no stack.
-/

namespace VG.Impl.Rc4.X86_64

open VG.X86_64

/-- `[base + offset]`. -/
def at_ (base : Reg) (offset : Nat) : MemOp := { base, disp := Int.ofNat offset }

/-- `[base + index]`. -/
def atIdx (base index : Reg) : MemOp := { base, index := some index }

/-- An immediate. -/
def imm (n : Nat) : Src := .imm (BitVec.ofNat 32 n)

/-- `r10` := all ones if `r9 XOR 8k < 8` (byte `r9` is in quadword `k`), else 0. -/
def rowMask (k : Nat) : List Instr :=
  [.mov .r10 (.reg .r9), .alu .xor .r10 (imm (8 * k)), .alu .sub .r10 (imm 8),
   .alu .sbb .r10 (.reg .r10)]

/-- `r10` := all ones if `r9 AND 7 = j`, else 0. -/
def laneMask (j : Nat) : List Instr :=
  [.mov .r10 (.reg .r9), .alu .and .r10 (imm 7), .alu .xor .r10 (imm j),
   .alu .sub .r10 (imm 1), .alu .sbb .r10 (.reg .r10)]

/-- Keep quadword `k` in `r11` if it holds byte `r9`. -/
def gatherStep (k : Nat) : List Instr :=
  rowMask k ++ ([.alu .and .r10 (.mem (at_ .rdi (8 * k))), .alu .or .r11 (.reg .r10)] : List Instr)

/-- Keep byte `j` of the quadword in `r11` (shifted down by `8j` so far) in `rax`
if it is byte `r9`. -/
def pickStep (j : Nat) : List Instr :=
  laneMask j ++ ([.alu .and .r10 (.reg .r11), .alu .or .rax (.reg .r10), .shift .shr .r11 8] :
    List Instr)

/-- The byte of the table at `rdi` indexed by the low byte `r9`, into `rax`.
Clobbers `r10`, `r11` and the flags. -/
def lookup : List Instr :=
  ([.mov .r11 (imm 0)] : List Instr) ++ (List.range 32).flatMap gatherStep ++
    ([.mov .rax (imm 0)] : List Instr) ++ (List.range 8).flatMap pickStep ++
    ([.alu .and .rax (imm 255)] : List Instr)

/-- Shift the difference in `r11` up a byte and add the byte in `rax` if `j`
is the lane of `r9`: run for `j` from 7 down to 0, it leaves `rax` shifted to
the lane of `r9`. -/
def spreadStep (j : Nat) : List Instr :=
  laneMask j ++ ([.alu .and .r10 (.reg .rax), .shift .ror .r11 56, .alu .or .r11 (.reg .r10)] :
    List Instr)

/-- XOR quadword `k` with the difference in `r11` if it holds byte `r9`, and
store it back. -/
def scatterStep (k : Nat) : List Instr :=
  rowMask k ++ ([.alu .and .r10 (.reg .r11), .alu .xor .r10 (.mem (at_ .rdi (8 * k))),
    .store (at_ .rdi (8 * k)) .r10] : List Instr)

/-- The lanes 7 down to 0. -/
def lanesDown : List Nat := [7, 6, 5, 4, 3, 2, 1, 0]

/-- Replace the byte of the table at `rdi` indexed by the low byte of `r9`
with the byte at the public index `rcx`, returning its original value in
`rax`. Clobbers `r10`, `r11` and the flags. -/
def replace : List Instr :=
  lookup ++
    ([.movzx8 .r11 (atIdx .rdi .rcx), .alu .xor .rax (.reg .r11), .mov .r11 (imm 0)] :
      List Instr) ++
    lanesDown.flatMap spreadStep ++
    ([.movzx8 .r10 (atIdx .rdi .rcx), .alu .xor .rax (.reg .r10)] : List Instr) ++
    (List.range 32).flatMap scatterStep

/-- Store the identity permutation, a byte at a time. -/
def identityStep : List Instr :=
  [.store8 (atIdx .rdi .rcx) .rcx, .alu .add .rcx (imm 1), .alu .cmp .rcx (imm 256)]

/-- `j += S[i] + key[off]`, the swap, then the next key offset (0 at the key
length, without a branch: `r10` is zeroed first, so that the mask `sbb` makes
of it is visibly public) and `i`. -/
def scheduleStep : List Instr :=
  ([.movzx8 .r10 (atIdx .rdi .rcx), .alu .add .r9 (.reg .r10),
    .movzx8 .r10 (atIdx .rsi .r8), .alu .add .r9 (.reg .r10), .alu .and .r9 (imm 255)] :
      List Instr) ++ replace ++
    ([.store8 (atIdx .rdi .rcx) .rax,
      .alu .add .r8 (imm 1), .mov .r10 (imm 0), .alu .cmp .r8 (.reg .rdx),
      .alu .sbb .r10 (.reg .r10),
      .alu .and .r8 (.reg .r10),
      .alu .add .rcx (imm 1), .alu .cmp .rcx (imm 256)] : List Instr)

/-- Key scheduling after the key-length check: the context to `rdi`, the key
to `rsi` and its length to `rdx`. -/
def initValid : Prog isa :=
  .seq (.block [.mov .rax (.reg .rdi), .mov .rdi (.reg .rdx), .mov .rdx (.reg .rsi),
      .mov .rsi (.reg .rax), .mov .rcx (imm 0)])
    (.seq (.loop (.block identityStep) .ne)
      (.seq (.block [.mov .rcx (imm 0), .mov .r8 (imm 0), .mov .r9 (imm 0)])
        (.seq (.loop (.block scheduleStep) .ne)
          (.block [.mov .rax (imm 0), .store8 (at_ .rdi 256) .rax,
            .store8 (at_ .rdi 257) .rax]))))

/-- Checked key scheduling: CF is set by `key_len - 1 < 256`; invalid
lengths return 1, valid lengths 0. -/
def init : Prog isa :=
  .seq (.block [.mov .rax (.reg .rsi), .alu .sub .rax (imm 1), .alu .cmp .rax (imm 256)])
    (.ite .ae (.block [.mov .rax (imm 1)]) initValid)

/-- One PRGA step: `i += 1`, `j += S[i]`, the swap, then the keystream byte
`S[S[i] + S[j]]` XORed into the next data byte. -/
def applyStep : List Instr :=
  ([.alu .add .rcx (imm 1), .alu .and .rcx (imm 255),
    .movzx8 .r10 (atIdx .rdi .rcx), .alu .add .r8 (.reg .r10), .alu .and .r8 (imm 255),
    .mov .r9 (.reg .r8)] : List Instr) ++ replace ++
    ([.movzx8 .r10 (atIdx .rdi .rcx), .store8 (atIdx .rdi .rcx) .rax,
      .alu .add .rax (.reg .r10), .alu .and .rax (imm 255), .mov .r9 (.reg .rax)] : List Instr) ++
    lookup ++
    ([.movzx8 .r10 (at_ .rsi 0), .alu .xor .r10 (.reg .rax), .store8 (at_ .rsi 0) .r10,
      .alu .add .rsi (imm 1), .alu .sub .rdx (imm 1)] : List Instr)

/-- Streaming XOR, preserving the permutation and both PRGA indices. The
indices are loaded first, and `len` tested. -/
def apply : Prog isa :=
  .seq (.block [.movzx8 .rcx (at_ .rdi 256), .movzx8 .r8 (at_ .rdi 257),
      .alu .test .rdx (.reg .rdx)])
    (.ite .e (.block [])
      (.seq (.loop (.block applyStep) .ne)
        (.block [.store8 (at_ .rdi 256) .rcx, .store8 (at_ .rdi 257) .r8])))

end VG.Impl.Rc4.X86_64
