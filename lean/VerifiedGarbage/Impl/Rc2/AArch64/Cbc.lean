import VerifiedGarbage.Impl.Rc2.AArch64.Block

/-! # RC2-CBC on baseline AArch64

The caller saves its callee-saved registers and link register outside the
block primitive's 256-byte scratch region. Decryption retains the input
ciphertext at scratch + 256 before overwriting it.
-/

namespace VG.Impl.Rc2.AArch64.Cbc

open VG.AArch64

def save : List Instr :=
  [.str .x .x23 .x4 264, .str .x .x24 .x4 272, .str .x .x30 .x4 280]

def setup : List Instr :=
  [rr .x23 .x1, rr .x24 .x3, rr .x1 .x2, rr .x2 .x4]

def restore : List Instr :=
  [.ldr .x .x23 .x2 264, .ldr .x .x24 .x2 272, .ldr .x .x30 .x2 280]

def before (d : Spec.Rc2.Direction) : List Instr :=
  match d with
  | .encrypt => [.ldr .x .x8 .x1 0, .ldr .x .x9 .x23 0,
      .logic .eor .x .x8 .x8 .x9, .str .x .x8 .x1 0]
  | .decrypt => [.ldr .x .x8 .x1 0, .str .x .x8 .x2 256]

def after (d : Spec.Rc2.Direction) : List Instr :=
  match d with
  | .encrypt => [.ldr .x .x8 .x1 0, .str .x .x8 .x23 0]
  | .decrypt => [.ldr .x .x8 .x1 0, .ldr .x .x9 .x23 0,
      .logic .eor .x .x8 .x8 .x9, .str .x .x8 .x1 0,
      .ldr .x .x8 .x2 256, .str .x .x8 .x23 0]

def advance : List Instr := [.addImm .x .x1 .x1 8, .subImm .x .x24 .x24 1]

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
    (.seq (.ite (.zero .x .x24) (.block []) (.loop (body d) (.nonzero .x .x24))) (.block restore))

def encrypt : Prog isa := cbc .encrypt

def decrypt : Prog isa := cbc .decrypt

end VG.Impl.Rc2.AArch64.Cbc
