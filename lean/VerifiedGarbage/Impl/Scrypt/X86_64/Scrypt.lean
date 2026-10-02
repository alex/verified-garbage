import VerifiedGarbage.Impl.Scrypt.X86_64.RoMix

/-!
# scrypt: x86-64 implementation

`scrypt(password = rdi, password_len = rsi, salt = rdx, salt_len = rcx,
r = r8, b = r9, blen, v, vlen, scratch, slen, out, out_len)`, the last seven
on the stack, computes scrypt (RFC 7914 §6) with `N = vlen / r` and
`p = blen / r`:

1. `B = PBKDF2-HMAC-SHA256 (P, S, 1, 128 blen)` into `b`, by a call of
   `vg_pbkdf2_hmac_sha256` (or the implementation `pbk` of it given);
2. `vg_scrypt_romix` on each of the `p` blocks of `128 r` bytes of `b`, with
   `v` as `V` and the start of `scratch` (`r + 2` chunks) as its working space;
3. `PBKDF2-HMAC-SHA256 (P, B, 1, out_len)` into `out`, by another call.

Both calls of PBKDF2 use the start of `scratch` (1600 bytes) as its working
space.

Everything runs in one stack frame of seven words, pushed from `r9`, `r8`,
`rsi`, `rdi` and three copies of `rax`: from `rsp`, PBKDF2's two stack
arguments (`out_len` and `scratch`), the block ROMix works on next, then the
password, its length, `r` and `b`, which the calls cannot change. Our own
stack arguments are above the frame and the return address, from
`rsp + 64`. The calls use the 32 bytes below the frame.

Only the pointers and the lengths affect timing: the only branch is on the
block pointer, and every address is in the frame (`rsp` plus a constant).
-/

namespace VG.Impl.Scrypt.X86_64

open VG.X86_64

/-- `[rsp + d]`. -/
def sp (d : Nat) : MemOp := { base := .rsp, disp := d }

/-- `d ← 128 d`, by rotating left by 7 (right by 57): the lengths here are less
than `2^57`. -/
def times128 (d : Reg) : Instr := .shift .ror d 57

/-- The arguments of the first PBKDF2 but those still in their registers
(the password, the salt and `out = b`): `c = 1`, and `out_len = 128 blen` and
`scratch` on the stack. -/
def pbk1Args : List Instr :=
  [.mov .rax (.mem (sp 64)), times128 .rax, .mov .r8 (.mem (sp 88)), .store (sp 0) .rax,
    .store (sp 8) .r8, .mov32 .r8 (.imm 1)]

/-- The first block. -/
def cur0 : List Instr := [.mov .rax (.mem (sp 48)), .store (sp 16) .rax]

/-- `romix(block, r, v, vlen, scratch, r + 2)`. -/
def romixArgs : List Instr :=
  [.mov .rdi (.mem (sp 16)), .mov .rsi (.mem (sp 40)), .mov .rdx (.mem (sp 72)),
    .mov .rcx (.mem (sp 80)), .mov .r8 (.mem (sp 88)), .mov .r9 (.reg .rsi), .alu .add .r9 (.imm 2)]

/-- The next block, `128 r` bytes on; `ZF` is set if it is the end of `b`
(`b + 128 blen`). -/
def nextBlock : List Instr :=
  [.mov .rcx (.mem (sp 40)), times128 .rcx, .mov .rax (.mem (sp 16)), .alu .add .rax (.reg .rcx),
    .mov .rdx (.mem (sp 64)), times128 .rdx, .alu .add .rdx (.mem (sp 48)), .store (sp 16) .rax,
    .alu .cmp .rax (.reg .rdx)]

/-- The arguments of the second PBKDF2: the password, `b` as the salt
(`128 blen` bytes), `c = 1`, `out`, and `out_len` and `scratch` on the stack. -/
def pbk2Args : List Instr :=
  [.mov .rdi (.mem (sp 24)), .mov .rsi (.mem (sp 32)), .mov .rdx (.mem (sp 48)),
    .mov .rcx (.mem (sp 64)), times128 .rcx, .mov .r9 (.mem (sp 104)), .mov .rax (.mem (sp 112)),
    .mov .r8 (.mem (sp 88)), .store (sp 0) .rax, .store (sp 8) .r8, .mov32 .r8 (.imm 1)]

/-- ROMix on each block. -/
def romixLoop : Prog isa :=
  .loop (.seq (.block romixArgs) (.seq (.call "vg_scrypt_romix" roMix) (.block nextBlock))) .ne

/-- A call of the implementation `pbk` of PBKDF2-HMAC-SHA256, named
`pbkName`, after the moves `args` of its arguments. -/
def pbkCall (pbkName : String) (pbk : Prog isa) (args : List Instr) : Prog isa :=
  .seq (.block args) (.call pbkName pbk)

/-- The frame's body, with the implementation `pbk` of PBKDF2-HMAC-SHA256,
named `pbkName`. -/
def scryptBody (pbkName : String) (pbk : Prog isa) : Prog isa :=
  .seq (pbkCall pbkName pbk pbk1Args) (.seq (.block cur0) (.seq romixLoop (pbkCall pbkName pbk pbk2Args)))

/-- `vg_scrypt`, calling the implementation `pbk` of PBKDF2-HMAC-SHA256,
named `pbkName`. -/
def scrypt (pbkName : String) (pbk : Prog isa) : Prog isa :=
  .frame (.push [.r9, .r8, .rsi, .rdi, .rax, .rax, .rax]) (scryptBody pbkName pbk) (.pop .rax 7)

end VG.Impl.Scrypt.X86_64
