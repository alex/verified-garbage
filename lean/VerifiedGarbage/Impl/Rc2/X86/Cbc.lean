import VerifiedGarbage.Impl.Rc2.X86.Block

/-! # RC2-CBC on baseline x86

EBX, ECX, ESI, EDI and EBP hold the schedule, IV, data, remaining block
count and scratch pointer. The block primitive preserves these registers.
Calls push three cdecl arguments and use 16 bytes of stack in total.
-/

namespace VG.Impl.Rc2.X86.Cbc

open VG.X86

def save : List Instr :=
  [.store (memOp .eax 264) .ebp, .store (memOp .eax 268) .ebx,
    .store (memOp .eax 272) .esi, .store (memOp .eax 276) .edi]

def setup : List Instr :=
  [rr .ebp .eax, .mov .ebx (.mem (memOp .esp 4)), .mov .ecx (.mem (memOp .esp 8)),
    .mov .esi (.mem (memOp .esp 12)), .mov .edi (.mem (memOp .esp 16)), .alu .cmp .edi (.imm 0)]

def restore : List Instr :=
  [rr .eax .ebp, .mov .ebp (.mem (memOp .eax 264)), .mov .ebx (.mem (memOp .eax 268)),
    .mov .esi (.mem (memOp .eax 272)), .mov .edi (.mem (memOp .eax 276))]

def copy64 (src dst : Reg) (a b : Nat) : List Instr :=
  [.mov .eax (.mem (memOp src a)), .mov .edx (.mem (memOp src (a + 4))),
    .store (memOp dst b) .eax, .store (memOp dst (b + 4)) .edx]

def xor64 (dst iv : Reg) : List Instr :=
  [.mov .eax (.mem (memOp dst 0)), .mov .edx (.mem (memOp dst 4)),
    .alu .xor .eax (.mem (memOp iv 0)), .alu .xor .edx (.mem (memOp iv 4)),
    .store (memOp dst 0) .eax, .store (memOp dst 4) .edx]

def before (d : Spec.Rc2.Direction) : List Instr :=
  match d with
  | .encrypt => xor64 .esi .ecx
  | .decrypt => copy64 .esi .ebp 0 256

def after (d : Spec.Rc2.Direction) : List Instr :=
  match d with
  | .encrypt => copy64 .esi .ecx 0 0
  | .decrypt => xor64 .esi .ecx ++ copy64 .ebp .ecx 256 0

def advance : List Instr :=
  [.alu .add .esi (.imm 8), .alu .sub .edi (.imm 1)]

def blockCall (d : Spec.Rc2.Direction) : Prog isa :=
  .frame (.push [.ebp, .esi, .ebx])
    (match d with
      | .encrypt => .call "vg_rc2_encrypt_block" encryptBlock
      | .decrypt => .call "vg_rc2_decrypt_block" decryptBlock)
    (.pop .eax 3)

def step (d : Spec.Rc2.Direction) : Prog isa :=
  .seq (.block (before d)) (.seq (blockCall d) (.block (after d)))

def body (d : Spec.Rc2.Direction) : Prog isa :=
  .seq (step d) (.block advance)

def cbc (d : Spec.Rc2.Direction) : Prog isa :=
  .seq (.block [.mov .eax (.mem (memOp .esp 20))])
    (.seq (.block (save ++ setup))
      (.seq (.ite .e (.block []) (.loop (body d) .ne)) (.block restore)))

def encrypt : Prog isa := cbc .encrypt
def decrypt : Prog isa := cbc .decrypt

end VG.Impl.Rc2.X86.Cbc
