import VerifiedGarbage.Impl.Rc2.Arm.Block

/-! # RC2-CBC on ARMv7

The caller saves its callee-saved registers and link register outside the
block primitive's 256-byte scratch region. Decryption retains the input
ciphertext at scratch + 256 before overwriting it.
-/

namespace VG.Impl.Rc2.Arm.Cbc

open VG.Arm

def save : List Instr :=
  [.str .r4 .r12 264, .str .r5 .r12 268, .str .r6 .r12 272,
   .str .r7 .r12 276, .str .lr .r12 280]

def setup : List Instr :=
  [rr .r4 .r1, rr .r5 .r3, rr .r1 .r2, rr .r2 .r12, .cmp .r5 (.imm 0)]

def restore : List Instr :=
  [.ldr .r4 .r2 264, .ldr .r5 .r2 268, .ldr .r6 .r2 272,
   .ldr .r7 .r2 276, .ldr .lr .r2 280]

def copy64 (src dst : Reg) (a b : Nat) : List Instr :=
  [.ldr .r12 src a, .ldr .r3 src (a + 4), .str .r12 dst b, .str .r3 dst (b + 4)]

def xor64 (dst iv : Reg) : List Instr :=
  [.ldr .r12 dst 0, .ldr .r3 dst 4, .ldr .r6 iv 0, .ldr .r7 iv 4,
   .dp .eor .r12 .r12 (.reg .r6), .dp .eor .r3 .r3 (.reg .r7),
   .str .r12 dst 0, .str .r3 dst 4]

def before (d : Spec.Rc2.Direction) : List Instr :=
  match d with
  | .encrypt => xor64 .r1 .r4
  | .decrypt => copy64 .r1 .r2 0 256

def after (d : Spec.Rc2.Direction) : List Instr :=
  match d with
  | .encrypt => copy64 .r1 .r4 0 0
  | .decrypt => xor64 .r1 .r4 ++ copy64 .r2 .r4 256 0

def advance : List Instr :=
  [.dp .add .r1 .r1 (.imm 8), .dp .sub .r5 .r5 (.imm 1), .cmp .r5 (.imm 0)]

def blockCall (d : Spec.Rc2.Direction) : Prog isa :=
  match d with
  | .encrypt => .call "vg_rc2_encrypt_block" encryptBlock
  | .decrypt => .call "vg_rc2_decrypt_block" decryptBlock

def step (d : Spec.Rc2.Direction) : Prog isa :=
  .seq (.block (before d)) (.seq (blockCall d) (.block (after d)))

def body (d : Spec.Rc2.Direction) : Prog isa :=
  .seq (step d) (.block advance)

def cbc (d : Spec.Rc2.Direction) : Prog isa :=
  .seq (.block [.ldrSp .r12 0])
    (.seq (.block (save ++ setup))
      (.seq (.ite .eq (.block []) (.loop (body d) .ne)) (.block restore)))

def encrypt : Prog isa := cbc .encrypt

def decrypt : Prog isa := cbc .decrypt

end VG.Impl.Rc2.Arm.Cbc
