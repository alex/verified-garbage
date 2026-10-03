import VerifiedGarbage.Impl.Scrypt.AArch64.RoMix

/-!
# scrypt: AArch64 implementation

`scrypt(password = x0, password_len = x1, salt = x2, salt_len = x3, r = x4,
b = x5, blen = x6, v = x7, vlen, scratch, slen, out, out_len)`, the last
five on the stack, computes scrypt (RFC 7914 §6) with `N = vlen / r` and
`p = blen / r`, as on x86-64 (`Impl/Scrypt/X86_64/Scrypt.lean`):

1. `B = PBKDF2-HMAC-SHA256 (P, S, 1, 128 blen)` into `b`, by a call of
   `vg_pbkdf2_hmac_sha256` (or the implementation `pbk` of it given);
2. `vg_scrypt_romix` on each of the `p` blocks of `128 r` bytes of `b`, with
   `v` as `V` and the start of `scratch` (`r + 2` chunks) as its working space;
3. `PBKDF2-HMAC-SHA256 (P, B, 1, out_len)` into `out`, by another call.

Both calls of PBKDF2 use the start of `scratch` (1600 bytes) as its working
space.

The function runs in two frames: one saving our return address `x30`, and
in it a 64-byte one holding, from `sp`, the block ROMix works on next, then
the password, its length, `r`, `b`, `blen` and `v`, which the calls cannot
change. Our own stack arguments are above both frames, from `sp + 80`. The
calls use the 16 bytes below the frames.

Only the pointers and the lengths affect timing: the only branch is on the
bytes of `b` left, and every address is in the frames (`sp` plus a
constant).
-/

namespace VG.Impl.Scrypt.AArch64

open VG.AArch64

/-- Keeping our arguments in the frame: `x15 = sp`. -/
def saveArgs : List Instr :=
  [.addSp .x15 0, .str .x .x0 .x15 8, .str .x .x1 .x15 16, .str .x .x4 .x15 24, .str .x .x5 .x15 32,
    .str .x .x6 .x15 40, .str .x .x7 .x15 48]

/-- The arguments of the first PBKDF2 but those still in their registers
(the password, the salt and `out = b`): `c = 1`, `out_len = 128 blen` and
`scratch`. -/
def pbk1Args : List Instr := [.movz .x .x4 1 0, .lsl .x .x6 .x6 7, .ldrSp .x7 88]

/-- The first block. -/
def cur0 : List Instr := [.ldrSp .x9 32, .addSp .x15 0, .str .x .x9 .x15 0]

/-- `romix(block, r, v, vlen, scratch, r + 2)`. -/
def romixArgs : List Instr :=
  [.ldrSp .x0 0, .ldrSp .x1 24, .ldrSp .x2 48, .ldrSp .x3 80, .ldrSp .x4 88, .addImm .x .x5 .x1 2]

/-- The next block, `128 r` bytes on, and in `x11` the bytes of `b` after it
(`b + 128 blen` less it). -/
def nextBlock : List Instr :=
  [.ldrSp .x9 0, .ldrSp .x10 24, .lsl .x .x10 .x10 7, .add .x .x9 .x9 .x10, .ldrSp .x11 32,
    .ldrSp .x12 40, .lsl .x .x12 .x12 7, .add .x .x11 .x11 .x12, .sub .x .x11 .x11 .x9,
    .addSp .x15 0, .str .x .x9 .x15 0]

/-- The arguments of the second PBKDF2: the password, `b` as the salt
(`128 blen` bytes), `c = 1`, `out`, `out_len` and `scratch`. -/
def pbk2Args : List Instr :=
  [.ldrSp .x0 8, .ldrSp .x1 16, .ldrSp .x2 32, .ldrSp .x3 40, .lsl .x .x3 .x3 7, .movz .x .x4 1 0,
    .ldrSp .x5 104, .ldrSp .x6 112, .ldrSp .x7 88]

/-- ROMix on each block. -/
def romixLoop : Prog isa :=
  .loop (.seq (.block romixArgs) (.seq (.call "vg_scrypt_romix" roMix) (.block nextBlock)))
    (.nonzero .x .x11)

/-- A call of the implementation `pbk` of PBKDF2-HMAC-SHA256, named
`pbkName`, after the moves `args` of its arguments. -/
def pbkCall (pbkName : String) (pbk : Prog isa) (args : List Instr) : Prog isa :=
  .seq (.block args) (.call pbkName pbk)

/-- The inner frame's body, with the implementation `pbk` of
PBKDF2-HMAC-SHA256, named `pbkName`. -/
def scryptBody (pbkName : String) (pbk : Prog isa) : Prog isa :=
  .seq (.block saveArgs)
    (.seq (pbkCall pbkName pbk pbk1Args) (.seq (.block cur0) (.seq romixLoop (pbkCall pbkName pbk pbk2Args))))

/-- `vg_scrypt`, calling the implementation `pbk` of PBKDF2-HMAC-SHA256,
named `pbkName`. -/
def scrypt (pbkName : String) (pbk : Prog isa) : Prog isa :=
  .frame (.push .x30) (.frame (.alloc 64) (scryptBody pbkName pbk) (.free 64)) (.pop .x30)

end VG.Impl.Scrypt.AArch64
