import VerifiedGarbage.Impl.Pbkdf2.AArch64

/-!
# PBKDF2-HMAC-SHA-256: AArch64 implementation

`derive(password = x0, password_len = x1, salt = x2, salt_len = x3, c = w4,
out = x5, out_len = x6, scratch = x7)` writes
`PBKDF2-HMAC-SHA256 (P, S, c, out_len)` to `out` (`VG.Spec.Pbkdf2.pbkdf2`),
composed of calls of the verified SHA-256, HMAC-SHA-256 and PBKDF2
functions, as on x86-64 (`VG.Impl.Pbkdf2.X86_64.derive`):

1. A password longer than a block (64 bytes) is hashed first
   (`vg_sha256_init`, `vg_sha256_update`, `vg_sha256_finalize`), which gives
   the same HMAC key `K₀` (RFC 2104 §2).
2. `vg_hmac_sha256_init` sets up the streaming states of `K₀ ⊕ ipad` and
   `K₀ ⊕ opad`, and `vg_sha256_update` absorbs the salt into a copy of the
   inner one.
3. For each block `i = 1, 2, …` of the derived key: a copy of that state
   absorbs `INT (i)` (`vg_sha256_update`), `vg_hmac_sha256_finalize` gives
   `U₁`, `vg_pbkdf2_hmac_sha256_iterate` exclusive-ors `U₂, …, U_c` into
   `T = U₁`, and the first `min (32, bytes left)` bytes of `T` are copied
   to `out`.

The calls leave unknown values in `x30`, so our return address is saved in a
stack frame (16 bytes); `vg_hmac_sha256_finalize` and the `vg_sha256_finalize`
it calls push a frame each below it, so the function uses 48 bytes of stack.

`scratch` (2048 bytes) holds:

* `[0, 192)`: the key's inner and outer streaming states (as
  `vg_pbkdf2_hmac_sha256_iterate` takes them);
* `[192, 288)`: the inner state after the salt;
* `[288, 384)`: the state being worked on (the password's hash, then each
  block's inner state);
* `[384, 416)`: `T`; `[416, 420)`: `INT (i)`;
* `[424, 488)`: our caller's `x19`–`x26`;
* `[496, 528)`: the password's hash;
* `[528, 912)`: the working space of the functions we call but
  `vg_hmac_sha256_finalize`, whose working space is `[912, 1152)` (so the MAC
  it leaves in `[1088, 1120)` is `U₁`).

The functions we call preserve `x19`–`x28`: `x19` is `scratch` throughout,
`x25` is `out_len` and `x26` is `c`. While the key is set up, `x20` and `x21`
are the key and its length, `x22` and `x23` the salt and its length, and
`x24` is `out`. In the loop over the blocks, `x24` is where the next block
goes in `out`, `x20` is `i`, `x21` the number of bytes left, `x22` is `c - 1`
and `x23` is `64 + salt_len`, the length of what the salted state
represents.

`c` is a 32-bit argument, whose register's upper half is whatever the caller
left there (possibly secret): the prologue zero-extends it into `x26`. Every
branch and address depends only on the pointers, the lengths and `c`.
-/

namespace VG.Impl.Pbkdf2.AArch64

open VG.AArch64
open VG.Impl.Sha256.AArch64.Stream (mov)
open VG.Impl.Hmac.AArch64 (cp64)

/-- The callee-saved registers we use, and where they are saved in `scratch`.
`x19` is last: the epilogue reads the others through it. -/
def dSaved : List (Reg × Nat) :=
  [(.x20, 432), (.x21, 440), (.x22, 448), (.x23, 456), (.x24, 464), (.x25, 472), (.x26, 480),
    (.x19, 424)]

/-- Saving our caller's registers, and setting up ours. -/
def dPrologue : List Instr :=
  dSaved.map (fun (r, d) => .str .x r .x7 d) ++
    [mov .x19 .x7, mov .x20 .x0, mov .x21 .x1, mov .x22 .x2, mov .x23 .x3, mov .x24 .x5, mov .x25 .x6,
      .addImm .w .x26 .x4 0]

/-- A password longer than 64 bytes replaced by its hash: `x20 = scratch + 496`, `x21 = 32`. -/
def hashKey : Prog isa :=
  .seq (.block [.addImm .x .x0 .x19 288]) <|
  .seq (.call "vg_sha256_init" Impl.Sha256.AArch64.Stream.init) <|
  .seq (.block [.addImm .x .x0 .x19 288, .movz .x .x1 0 0, mov .x2 .x20, mov .x3 .x21,
    .addImm .x .x4 .x19 528]) <|
  .seq (.call "vg_sha256_update" Impl.Sha256.AArch64.Stream.update) <|
  .seq (.block [.addImm .x .x0 .x19 288, mov .x1 .x21, .addImm .x .x2 .x19 496, .addImm .x .x3 .x19 528]) <|
  .seq (.call "vg_sha256_finalize" Impl.Sha256.AArch64.Stream.finalize)
    (.block [.addImm .x .x20 .x19 496, .movz .x .x21 32 0])

/-- The key: the password, or its hash if it is longer than 64 bytes, which is
when `password_len ≠ 0` and `(password_len - 1) / 64 ≠ 0`. -/
def keyPrep : Prog isa :=
  .ite (.zero .x .x21) (.block [])
    (.seq (.block [.subImm .x .x9 .x21 1, .lsr .x .x9 .x9 6]) (.ite (.zero .x .x9) (.block []) hashKey))

/-- The key's streaming states, and the salt absorbed into a copy of the inner one. -/
def keySalt : Prog isa :=
  .seq (.block [mov .x0 .x19, .addImm .x .x1 .x19 96, mov .x2 .x20, mov .x3 .x21, .addImm .x .x4 .x19 528]) <|
  .seq (.call "vg_hmac_sha256_init" Impl.Hmac.AArch64.init) <|
  .seq (.block ((List.range 12).flatMap (cp64 .x19 .x19 0 192) ++
    [.addImm .x .x0 .x19 192, .movz .x .x1 64 0, mov .x2 .x22, mov .x3 .x23, .addImm .x .x4 .x19 528]))
    (.call "vg_sha256_update" Impl.Sha256.AArch64.Stream.update)

/-- The registers for the loop over the blocks. -/
def loopSetup : List Instr :=
  [.addImm .x .x23 .x23 64, .subImm .w .x22 .x26 1, .movz .x .x20 1 0, mov .x21 .x25]

/-- `U₁ = HMAC (P, S ‖ INT (i))`, left in `scratch[1088, 1120)`. -/
def blockU : Prog isa :=
  .seq (.block ((List.range 12).flatMap (cp64 .x19 .x19 192 288) ++
    [.rev32 .x9 .x20, .str .w .x9 .x19 416, .addImm .x .x0 .x19 288, mov .x1 .x23, .addImm .x .x2 .x19 416,
      .movz .x .x3 4 0, .addImm .x .x4 .x19 528])) <|
  .seq (.call "vg_sha256_update" Impl.Sha256.AArch64.Stream.update) <|
  .seq (.block [.addImm .x .x0 .x19 288, .addImm .x .x1 .x19 96, .addImm .x .x2 .x23 4,
    .addImm .x .x3 .x19 912])
    (.call "vg_hmac_sha256_finalize" Impl.Hmac.AArch64.finalize)

/-- `T = U₁ ⊕ U₂ ⊕ … ⊕ U_c` in `scratch[384, 416)`. -/
def blockT : Prog isa :=
  .seq (.block ((List.range 4).flatMap (cp64 .x19 .x19 1088 384) ++
    [mov .x0 .x19, .addImm .x .x1 .x19 1088, mov .x2 .x22, .addImm .x .x3 .x19 384,
      .addImm .x .x4 .x19 528]))
    (.call "vg_pbkdf2_hmac_sha256_iterate" iterate)

/-- The bytes `[x11] → [x24]`, `x9 > 0` of them. -/
def byteLoop : Prog isa :=
  .loop (.block [.ldrb .x10 .x11 0, .strb .x10 .x24 0, .addImm .x .x11 .x11 1, .addImm .x .x24 .x24 1,
    .subImm .x .x9 .x9 1]) (.nonzero .x .x9)

/-- The first `min (32, x21)` bytes of `T` to `x24`. -/
def blockOut : Prog isa :=
  .seq (.block [.movz .x .x9 32 0, .lsr .x .x10 .x21 5]) <|
  .seq (.ite (.zero .x .x10) (.block [mov .x9 .x21]) (.block [])) <|
  .seq (.block [.sub .x .x21 .x21 .x9, .addImm .x .x11 .x19 384]) <|
  .seq byteLoop (.block [.addImm .x .x20 .x20 1])

/-- One block of the derived key. -/
def block : Prog isa := .seq blockU (.seq blockT blockOut)

/-- Restoring our caller's registers. -/
def dEpilogue : List Instr := dSaved.map fun (r, d) => .ldr .x r .x19 d

/-- `derive`, but for saving `x30`. -/
def deriveMain : Prog isa :=
  .seq (.block dPrologue) <|
  .seq keyPrep <|
  .seq keySalt <|
  .seq (.block loopSetup) <|
  .seq (.ite (.zero .x .x21) (.block []) (.loop block (.nonzero .x .x21)))
    (.block dEpilogue)

def derive : Prog isa := .frame (.push .x30) deriveMain (.pop .x30)

end VG.Impl.Pbkdf2.AArch64
