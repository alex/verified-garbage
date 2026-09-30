import VerifiedGarbage.Impl.Rc2.X86_64.Block

/-! # RC2-CBC on baseline x86-64

The block functions preserve `rdi` (schedule), `rsi` (data), `rdx`
(scratch), `rbx` (IV pointer), and `rbp` (remaining blocks). The CBC
caller saves only `rbx` and `rbp`, outside the block function's 256-byte
scratch region. Decryption retains the input ciphertext at scratch + 256
before overwriting it. No branch or address depends on secret bytes.
-/

namespace VG.Impl.Rc2.X86_64.Cbc

open VG.X86_64

def save : List Instr :=
  [.store (memOp .r8 264) .rbx, .store (memOp .r8 272) .rbp]

def setup : List Instr :=
  [rr .rbx .rsi, rr .rbp .rcx, rr .rsi .rdx, rr .rdx .r8, .alu .cmp .rbp (.imm 0)]

def restore : List Instr :=
  [.mov .rbx (.mem (memOp .rdx 264)), .mov .rbp (.mem (memOp .rdx 272))]

def before (d : Spec.Rc2.Direction) : List Instr :=
  match d with
  | .encrypt => [.mov .rax (.mem (memOp .rsi 0)), .alu .xor .rax (.mem (memOp .rbx 0)),
      .store (memOp .rsi 0) .rax]
  | .decrypt => [.mov .rax (.mem (memOp .rsi 0)), .store (memOp .rdx 256) .rax]

def after (d : Spec.Rc2.Direction) : List Instr :=
  match d with
  | .encrypt => [.mov .rax (.mem (memOp .rsi 0)), .store (memOp .rbx 0) .rax]
  | .decrypt => [.mov .rax (.mem (memOp .rsi 0)), .alu .xor .rax (.mem (memOp .rbx 0)),
      .store (memOp .rsi 0) .rax, .mov .rax (.mem (memOp .rdx 256)), .store (memOp .rbx 0) .rax]

def advance : List Instr := [.alu .add .rsi (.imm 8), .alu .sub .rbp (.imm 1)]

def blockCall (d : Spec.Rc2.Direction) : Prog isa :=
  match d with
  | .encrypt => .call "vg_rc2_encrypt_block" encryptBlock
  | .decrypt => .call "vg_rc2_decrypt_block" decryptBlock

def step (d : Spec.Rc2.Direction) : Prog isa :=
  .seq (.block (before d)) (.seq (blockCall d) (.block (after d)))

def body (d : Spec.Rc2.Direction) : Prog isa :=
  .seq (step d) (.block advance)

def cbc (d : Spec.Rc2.Direction) : Prog isa :=
  .seq (.block (save ++ setup))
    (.seq (.ite .e (.block []) (.loop (body d) .ne)) (.block restore))

def encrypt : Prog isa := cbc .encrypt

def decrypt : Prog isa := cbc .decrypt

end VG.Impl.Rc2.X86_64.Cbc
