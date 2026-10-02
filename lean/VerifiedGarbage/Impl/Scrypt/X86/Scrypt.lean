import VerifiedGarbage.Impl.Scrypt.X86.RoMix
import VerifiedGarbage.Impl.Hmac.Generic.X86

/-!
# scrypt: x86 (32-bit) implementation

`scrypt(password, password_len, salt, salt_len, r, b, blen, v, vlen,
scratch, slen, out, out_len)`, every argument on the stack (cdecl), computes
scrypt (RFC 7914 §6) with `N = vlen / r` and `p = blen / r`, as on the other
targets (`Impl/Scrypt/X86_64/Scrypt.lean`):

1. `B = PBKDF2-HMAC-SHA256 (P, S, 1, 128 blen)` into `b`, by a call of
   `vg_pbkdf2_hmac_sha256` (or the implementation `pbk` of it given);
2. `vg_scrypt_romix` on each of the `p` blocks of `128 r` bytes of `b`, with
   `v` as `V` and the start of `scratch` (`r + 2` chunks) as its working space;
3. `PBKDF2-HMAC-SHA256 (P, B, 1, out_len)` into `out`, by another call.

Both calls of PBKDF2 use the start of `scratch` (1600 bytes) as its working
space.

The function runs in a frame of nine words (pushes of `eax`): from `esp`,
the arguments of the function it calls (eight words for PBKDF2, six for
ROMix), stored before each call, and the block ROMix works on next. Our own
arguments are above the frame and our return address, from `esp + 40`, and
are read whenever they are needed. Only `eax`, `ecx` and `edx` are used, so
our caller's `ebx`, `esi`, `edi` and `ebp` stay as they are. The calls use
the 80 bytes below the frame (PBKDF2's return address and its 76 bytes of
stack).

Only the pointers and the lengths affect timing: the only branch is on the
bytes of `b` left, and every address is in the frame or our arguments
(`esp` plus a constant).
-/

namespace VG.Impl.Scrypt.X86

open VG.X86
open VG.Impl.Hmac.Generic.X86 (at_)

/-- `[esp + d]`. -/
abbrev sp (d : Nat) : MemOp := at_ .esp d

/-- `d * 128`, for `d < 2^25`. -/
abbrev times128 (d : Reg) : Instr := .shift .ror d 25

/-- The arguments of the first PBKDF2: the password, the salt, `c = 1`,
`out = b`, `out_len = 128 blen` and `scratch`. -/
def pbk1Args : List Instr :=
  [.mov .eax (.mem (sp 40)), .store (sp 0) .eax, .mov .eax (.mem (sp 44)), .store (sp 4) .eax,
    .mov .eax (.mem (sp 48)), .store (sp 8) .eax, .mov .eax (.mem (sp 52)), .store (sp 12) .eax,
    .mov .eax (.imm 1), .store (sp 16) .eax, .mov .eax (.mem (sp 60)), .store (sp 20) .eax,
    .mov .eax (.mem (sp 64)), times128 .eax, .store (sp 24) .eax, .mov .eax (.mem (sp 76)),
    .store (sp 28) .eax]

/-- The first block. -/
def cur0 : List Instr := [.mov .eax (.mem (sp 60)), .store (sp 32) .eax]

/-- `romix(block, r, v, vlen, scratch, r + 2)`. -/
def romixArgs : List Instr :=
  [.mov .eax (.mem (sp 32)), .store (sp 0) .eax, .mov .eax (.mem (sp 56)), .store (sp 4) .eax,
    .mov .eax (.mem (sp 68)), .store (sp 8) .eax, .mov .eax (.mem (sp 72)), .store (sp 12) .eax,
    .mov .eax (.mem (sp 76)), .store (sp 16) .eax, .mov .eax (.mem (sp 56)), .alu .add .eax (.imm 2),
    .store (sp 20) .eax]

/-- The next block, `128 r` bytes on, compared with the end of `b`
(`b + 128 blen`). -/
def nextBlock : List Instr :=
  [.mov .ecx (.mem (sp 56)), times128 .ecx, .mov .eax (.mem (sp 32)), .alu .add .eax (.reg .ecx),
    .mov .edx (.mem (sp 64)), times128 .edx, .alu .add .edx (.mem (sp 60)), .store (sp 32) .eax,
    .alu .cmp .eax (.reg .edx)]

/-- The arguments of the second PBKDF2: the password, `b` as the salt
(`128 blen` bytes), `c = 1`, `out`, `out_len` and `scratch`. -/
def pbk2Args : List Instr :=
  [.mov .eax (.mem (sp 40)), .store (sp 0) .eax, .mov .eax (.mem (sp 44)), .store (sp 4) .eax,
    .mov .eax (.mem (sp 60)), .store (sp 8) .eax, .mov .eax (.mem (sp 64)), times128 .eax,
    .store (sp 12) .eax, .mov .eax (.imm 1), .store (sp 16) .eax, .mov .eax (.mem (sp 84)),
    .store (sp 20) .eax, .mov .eax (.mem (sp 88)), .store (sp 24) .eax, .mov .eax (.mem (sp 76)),
    .store (sp 28) .eax]

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

/-- The registers the frame's push stores. -/
abbrev pushRs : List Reg := [.eax, .eax, .eax, .eax, .eax, .eax, .eax, .eax, .eax]

/-- `vg_scrypt`, calling the implementation `pbk` of PBKDF2-HMAC-SHA256,
named `pbkName`. -/
def scrypt (pbkName : String) (pbk : Prog isa) : Prog isa :=
  .frame (.push pushRs) (scryptBody pbkName pbk) (.pop .eax 9)

end VG.Impl.Scrypt.X86
