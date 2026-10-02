import VerifiedGarbage.Impl.Scrypt.Arm.RoMix

/-!
# scrypt: 32-bit ARM implementation

`scrypt(password = r0, password_len = r1, salt = r2, salt_len = r3, r, b,
blen, v, vlen, scratch, slen, out, out_len)`, the last nine on the stack
(from `[sp]`), computes scrypt (RFC 7914 §6) with `N = vlen / r` and
`p = blen / r`, as on the other targets (`Impl/Scrypt/X86_64/Scrypt.lean`):

1. `B = PBKDF2-HMAC-SHA256 (P, S, 1, 128 blen)` into `b`, by a call of
   `vg_pbkdf2_hmac_sha256` (or the implementation `pbk` of it given);
2. `vg_scrypt_romix` on each of the `p` blocks of `128 r` bytes of `b`, with
   `v` as `V` and the start of `scratch` (`r + 2` chunks) as its working space;
3. `PBKDF2-HMAC-SHA256 (P, B, 1, out_len)` into `out`, by another call.

Both calls of PBKDF2 use the start of `scratch` (1600 bytes) as its working
space. The function has no stack frame of its own: our caller's `r4`–`r11`
and our return address are saved in the last of the `r + 16` chunks of
`scratch`, which neither callee touches (`r` is positive, so it starts at
`128 (r + 15) ≥ max (1600, 128 (r + 2))`); our return address goes through
the first word of `scratch` first, since only `r12` and `lr` are free before
the others are saved. Across the calls, which preserve them, `r4` is the
next block, `r5` the end of `b` (`b + 128 blen`), `r6` is `r`, `r7`
`scratch`, `r8` the password and `r9` its length. Each call's stack
arguments are pushed in a frame of their own (`push {r10, r11, r12, lr}` for
PBKDF2, `push {r12, lr}` for ROMix, as `vg_pbkdf2_hmac_sha256` does), so
that the stack pointer stays 8-byte aligned. PBKDF2 uses the 24 bytes below
its frame; ROMix uses no stack.

Only the pointers and the lengths affect timing: the only branch is on the
blocks left, and every address is a pointer argument plus a constant.
-/

namespace VG.Impl.Scrypt.Arm

open VG.Arm

/-- Our return address into the first word of `scratch`, in `r12`. -/
def save1 : List Instr := [.ldrSp .r12 20, .str .lr .r12 0]

/-- The save area, `scratch + 128 (r + 15)`, into `r12`, and our caller's
`r4`–`r11` into it. -/
def save2 : List Instr :=
  [.ldrSp .lr 0, .dp .add .r12 .r12 (.shifted .lr .lsl 7), .dp .add .r12 .r12 (.imm 1920),
    .str .r4 .r12 0, .str .r5 .r12 4, .str .r6 .r12 8, .str .r7 .r12 12, .str .r8 .r12 16,
    .str .r9 .r12 20, .str .r10 .r12 24, .str .r11 .r12 28]

/-- Our return address, from the first word of `scratch`, into the save area. -/
def save3 : List Instr := [.ldrSp .lr 20, .ldr .lr .lr 0, .str .lr .r12 32]

/-- The registers kept across the calls; then the arguments of the first
PBKDF2 (the password and the salt are still in `r0`–`r3`): `c = 1`,
`out = b`, `out_len = 128 blen` and `scratch`. -/
def pbk1Args : List Instr :=
  [.mov .r8 (.reg .r0), .mov .r9 (.reg .r1), .ldrSp .r6 0, .ldrSp .r7 20, .ldrSp .r4 4, .ldrSp .r5 8,
    .dp .add .r5 .r4 (.shifted .r5 .lsl 7), .mov .r10 (.imm 1), .mov .r11 (.reg .r4),
    .dp .sub .r12 .r5 (.reg .r4), .mov .lr (.reg .r7)]

/-- `romix(block, r, v, vlen, scratch, r + 2)`. -/
def romixArgs : List Instr :=
  [.mov .r0 (.reg .r4), .mov .r1 (.reg .r6), .ldrSp .r2 12, .ldrSp .r3 16, .mov .r12 (.reg .r7),
    .dp .add .lr .r6 (.imm 2)]

/-- The next block, `128 r` bytes on, compared with the end of `b`. -/
def nextBlock : List Instr := [.dp .add .r4 .r4 (.shifted .r6 .lsl 7), .cmp .r4 (.reg .r5)]

/-- The arguments of the second PBKDF2: the password, `b` as the salt
(`128 blen` bytes), `c = 1`, `out`, `out_len` and `scratch`. -/
def pbk2Args : List Instr :=
  [.mov .r0 (.reg .r8), .mov .r1 (.reg .r9), .ldrSp .r2 4, .ldrSp .r3 8, .mov .r3 (.shifted .r3 .lsl 7),
    .mov .r10 (.imm 1), .ldrSp .r11 28, .ldrSp .r12 32, .mov .lr (.reg .r7)]

/-- Our caller's registers and our return address, back from the save area. -/
def restore : List Instr :=
  [.dp .add .r12 .r7 (.shifted .r6 .lsl 7), .dp .add .r12 .r12 (.imm 1920), .ldr .r4 .r12 0,
    .ldr .r5 .r12 4, .ldr .r6 .r12 8, .ldr .r7 .r12 12, .ldr .r8 .r12 16, .ldr .r9 .r12 20,
    .ldr .r10 .r12 24, .ldr .r11 .r12 28, .ldr .lr .r12 32]

/-- A call of the implementation `pbk` of PBKDF2-HMAC-SHA256, named
`pbkName`, with its stack arguments `r10`, `r11`, `r12` and `lr`. -/
def pbkCall (pbkName : String) (pbk : Prog isa) : Prog isa :=
  .frame (.push [.r10, .r11, .r12, .lr]) (.call pbkName pbk) (.pop .r12 16)

/-- ROMix on each block. -/
def romixLoop : Prog isa :=
  .loop (.seq (.block romixArgs)
    (.seq (.frame (.push [.r12, .lr]) (.call "vg_scrypt_romix" roMix) (.pop .r12 8)) (.block nextBlock))) .ne

/-- `vg_scrypt`, calling the implementation `pbk` of PBKDF2-HMAC-SHA256,
named `pbkName`. -/
def scrypt (pbkName : String) (pbk : Prog isa) : Prog isa :=
  .seq (.block save1)
  (.seq (.block save2)
  (.seq (.block save3)
  (.seq (.block pbk1Args)
  (.seq (pbkCall pbkName pbk)
  (.seq romixLoop
  (.seq (.block pbk2Args)
  (.seq (pbkCall pbkName pbk)
    (.block restore))))))))

end VG.Impl.Scrypt.Arm
