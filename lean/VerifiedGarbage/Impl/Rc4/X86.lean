import VerifiedGarbage.TCB.X86.Isa

/-!
# RC4 on baseline x86 (32-bit)

As on x86-64 (`Impl/Rc4/X86_64.lean`), with the 256-byte table at `edi`
visited as 64 doublewords: a secret-indexed lookup keeps, with masks made by
`sub` and `sbb`, the doubleword that holds the byte and then the byte of it;
a secret-indexed replacement stores every doubleword back, XORed with a
masked difference that is nonzero only in the selected byte. Only the
doubleword addresses, the PRGA index `i`, the key offset, the pointers and
the lengths are public.

Every argument is on the stack (cdecl), and no stack is used below them:
our caller's `ebx`, `esi`, `edi` and `ebp` are saved in the first 16 bytes
of `scratch` (the stream function keeps `j` at `scratch[16]` during the
keystream lookup) and restored from it at the end. Registers: the table at `edi`, the public index `i` in `esi`, the
secret index of a lookup or replacement in `ebp`, its result in `eax`;
`ecx` and `edx` are scratch. Initialization keeps the key offset in `ebx`
and `j` in `ebp`; the stream function keeps the count of bytes done in
`ebx` and `j` in `ebp`. Both read the other arguments from the stack.
-/

namespace VG.Impl.Rc4.X86

open VG.X86

/-- `[base + offset]`. -/
def at_ (base : Reg) (offset : Nat) : MemOp := { base, disp := offset }

/-- An immediate. -/
def imm (n : Nat) : Src := .imm (BitVec.ofNat 32 n)

/-- `edx` := all ones if `ebp XOR 4k < 4` (byte `ebp` is in doubleword `k`), else 0. -/
def rowMask (k : Nat) : List Instr :=
  [.mov .edx (.reg .ebp), .alu .xor .edx (imm (4 * k)), .alu .sub .edx (imm 4),
   .alu .sbb .edx (.reg .edx)]

/-- `edx` := all ones if `ebp AND 3 = j`, else 0. -/
def laneMask (j : Nat) : List Instr :=
  [.mov .edx (.reg .ebp), .alu .and .edx (imm 3), .alu .xor .edx (imm j),
   .alu .sub .edx (imm 1), .alu .sbb .edx (.reg .edx)]

/-- Keep doubleword `k` in `ecx` if it holds byte `ebp`. -/
def gatherStep (k : Nat) : List Instr :=
  rowMask k ++ ([.alu .and .edx (.mem (at_ .edi (4 * k))), .alu .or .ecx (.reg .edx)] : List Instr)

/-- Keep byte `j` of the doubleword in `ecx` (shifted down by `8j` so far) in
`eax` if it is byte `ebp`. -/
def pickStep (j : Nat) : List Instr :=
  laneMask j ++ ([.alu .and .edx (.reg .ecx), .alu .or .eax (.reg .edx), .shift .shr .ecx 8] :
    List Instr)

/-- The byte of the table at `edi` indexed by the low byte `ebp`, into `eax`.
Clobbers `ecx`, `edx` and the flags. -/
def lookup : List Instr :=
  ([.mov .ecx (imm 0)] : List Instr) ++ (List.range 64).flatMap gatherStep ++
    ([.mov .eax (imm 0)] : List Instr) ++ (List.range 4).flatMap pickStep ++
    ([.alu .and .eax (imm 255)] : List Instr)

/-- Shift the difference in `ecx` up a byte and add the byte in `eax` if `j`
is the lane of `ebp`. -/
def spreadStep (j : Nat) : List Instr :=
  laneMask j ++ ([.alu .and .edx (.reg .eax), .shift .ror .ecx 24, .alu .or .ecx (.reg .edx)] :
    List Instr)

/-- XOR doubleword `k` with the difference in `ecx` if it holds byte `ebp`,
and store it back. -/
def scatterStep (k : Nat) : List Instr :=
  rowMask k ++ ([.alu .and .edx (.reg .ecx), .alu .xor .edx (.mem (at_ .edi (4 * k))),
    .store (at_ .edi (4 * k)) .edx] : List Instr)

/-- The lanes 3 down to 0. -/
def lanesDown : List Nat := [3, 2, 1, 0]

/-- `edx` := the byte at the public index `esi` of the table. -/
def loadI : List Instr := [.mov .edx (.reg .edi), .alu .add .edx (.reg .esi), .movzx8 .edx (at_ .edx 0)]

/-- Replace the byte of the table at `edi` indexed by the low byte of `ebp`
with the byte at the public index `esi`, returning its original value in
`eax`. Clobbers `ecx`, `edx` and the flags. -/
def replace : List Instr :=
  lookup ++ loadI ++ ([.alu .xor .eax (.reg .edx), .mov .ecx (imm 0)] : List Instr) ++
    lanesDown.flatMap spreadStep ++ loadI ++ ([.alu .xor .eax (.reg .edx)] : List Instr) ++
    (List.range 64).flatMap scatterStep

/-! ## Our caller's registers -/

/-- Save our caller's `ebx`, `esi`, `edi` and `ebp` at the start of `scratch`
(the fourth argument), through `ecx`. -/
def save : List Instr :=
  [.mov .ecx (.mem (at_ .esp 16)), .store (at_ .ecx 0) .ebx, .store (at_ .ecx 4) .esi,
   .store (at_ .ecx 8) .edi, .store (at_ .ecx 12) .ebp]

/-- Restore them, through `ecx`. -/
def restore : List Instr :=
  [.mov .ecx (.mem (at_ .esp 16)), .mov .ebx (.mem (at_ .ecx 0)), .mov .esi (.mem (at_ .ecx 4)),
   .mov .edi (.mem (at_ .ecx 8)), .mov .ebp (.mem (at_ .ecx 12))]

/-! ## Initialization: `vg_rc4_init(key, key_len, ctx, scratch)` -/

/-- Store the identity permutation, a byte at a time. -/
def identityStep : List Instr :=
  [.mov .edx (.reg .edi), .alu .add .edx (.reg .esi), .mov .eax (.reg .esi),
   .store8 (at_ .edx 0) .al, .alu .add .esi (imm 1), .alu .cmp .esi (imm 256)]

/-- `j += S[i] + key[off]`, the swap (`S[i]` stored after the key length is
read), the next key offset (0 at the key
length, without a branch: `edx` is zeroed after the comparison, so that the
mask `sbb` makes of it is visibly public), and `i`. The arguments are loaded
into a register before they are compared: the analysis of constant time
follows public values in memory only through `mov`. -/
def scheduleStep : List Instr :=
  loadI ++ ([.alu .add .ebp (.reg .edx), .mov .edx (.mem (at_ .esp 4)), .alu .add .edx (.reg .ebx),
    .movzx8 .edx (at_ .edx 0), .alu .add .ebp (.reg .edx), .alu .and .ebp (imm 255)] : List Instr) ++
    replace ++
    ([.alu .add .ebx (imm 1), .mov .edx (.mem (at_ .esp 8)), .alu .cmp .ebx (.reg .edx),
      .mov .edx (imm 0), .alu .sbb .edx (.reg .edx), .alu .and .ebx (.reg .edx),
      .mov .edx (.reg .edi), .alu .add .edx (.reg .esi), .store8 (at_ .edx 0) .al,
      .alu .add .esi (imm 1), .alu .cmp .esi (imm 256)] : List Instr)

/-- Key scheduling after the key-length check. -/
def initValid : Prog isa :=
  .seq (.block (save ++ ([.mov .edi (.mem (at_ .esp 12)), .mov .esi (imm 0)] : List Instr)))
    (.seq (.loop (.block identityStep) .ne)
      (.seq (.block [.mov .esi (imm 0), .mov .ebx (imm 0), .mov .ebp (imm 0)])
        (.seq (.loop (.block scheduleStep) .ne)
          (.block (([.mov .eax (imm 0), .store8 (at_ .edi 256) .al, .store8 (at_ .edi 257) .al] :
            List Instr) ++ restore)))))

/-- Checked key scheduling: CF is set by `key_len - 1 < 256`; invalid
lengths return 1, valid lengths 0. -/
def init : Prog isa :=
  .seq (.block [.mov .eax (.mem (at_ .esp 8)), .alu .sub .eax (imm 1), .alu .cmp .eax (imm 256)])
    (.ite .ae (.block [.mov .eax (imm 1)]) initValid)

/-! ## The stream function: `vg_rc4_apply(ctx, data, len, scratch)` -/

/-- The PRGA index `i` to `eax`, and the length tested. -/
def entry : List Instr :=
  [.mov .edx (.mem (at_ .esp 4)), .movzx8 .eax (at_ .edx 256), .mov .ecx (.mem (at_ .esp 12)),
   .alu .test .ecx (.reg .ecx)]

/-- The table to `edi`, the PRGA indices to `esi` and `ebp`, and no bytes done in `ebx`. -/
def start : List Instr :=
  [.mov .esi (.reg .eax), .mov .edi (.mem (at_ .esp 4)), .movzx8 .ebp (at_ .edi 257),
   .mov .ebx (imm 0)]

/-- One PRGA step: `i += 1`, `j += S[i]`, the swap, then the keystream byte
`S[S[i] + S[j]]` (with `j` kept in `scratch[16]` meanwhile) XORed into data
byte `ebx`. -/
def applyStep : List Instr :=
  ([.alu .add .esi (imm 1), .alu .and .esi (imm 255)] : List Instr) ++ loadI ++
    ([.alu .add .ebp (.reg .edx), .alu .and .ebp (imm 255)] : List Instr) ++ replace ++ loadI ++
    ([.mov .ecx (.reg .edi), .alu .add .ecx (.reg .esi), .store8 (at_ .ecx 0) .al,
      .alu .add .eax (.reg .edx), .alu .and .eax (imm 255),
      .mov .edx (.mem (at_ .esp 16)), .store (at_ .edx 16) .ebp, .mov .ebp (.reg .eax)] :
        List Instr) ++ lookup ++
    ([.mov .edx (.mem (at_ .esp 16)), .mov .ebp (.mem (at_ .edx 16)),
      .mov .edx (.mem (at_ .esp 8)), .alu .add .edx (.reg .ebx), .movzx8 .ecx (at_ .edx 0),
      .alu .xor .ecx (.reg .eax), .store8 (at_ .edx 0) .cl,
      .alu .add .ebx (imm 1), .mov .edx (.mem (at_ .esp 12)), .alu .cmp .ebx (.reg .edx)] :
        List Instr)

/-- Store the PRGA indices back. -/
def finish : List Instr :=
  [.mov .eax (.reg .esi), .store8 (at_ .edi 256) .al, .mov .eax (.reg .ebp),
   .store8 (at_ .edi 257) .al]

/-- Streaming XOR, preserving the permutation and both PRGA indices. `i`
is loaded first, while only caller-saved registers are written: the
function may leak it. -/
def apply : Prog isa :=
  .seq (.block entry)
    (.ite .e (.block [])
      (.seq (.block (save ++ start))
        (.seq (.loop (.block applyStep) .ne) (.block (finish ++ restore)))))

end VG.Impl.Rc4.X86
