import VerifiedGarbage.Impl.Hmac.Arm

/-!
# PBKDF2-HMAC-SHA-256's iteration: 32-bit ARM implementation

`iterate(key = r0, u = r1, n = r2, t = r3, scratch = [sp])` runs `n` steps
`U ← HMAC (K₀, U)`, `T ← T ⊕ U` (`VG.Spec.Pbkdf2.iterate`), for the key
whose inner and outer streaming states are at `key` and `key + 96`.

The same design as on x86-64 and AArch64 (`VG.Impl.Pbkdf2.X86_64`,
`VG.Impl.Pbkdf2.AArch64`): the inner and outer states have each absorbed one
block, so HMAC-SHA-256 of the 32-byte `U` is two compressions (calls of
`vg_sha256_compress`, through the streaming code's `compressAt`), each of one
block that is 32 bytes of message followed by the padding of a 96-byte
message.

`vg_sha256_compress` saves its callee-saved registers in its scratch space
and restores them, and the taint analysis only tracks memory at known offsets
from the base of a writable region. So the hash value being compressed is
`t` itself (the base of a writable region, in `r0`) and the compression's
scratch space is the start of `scratch` (in `r3`), while `T` is kept in
`scratch` and copied back to `t` at the end. `scratch` holds the
compression's scratch space (`[0..112)`), our caller's `r4`–`r11` and our
return address (`[112..148)`, where the streaming code's `save` and
`restore` keep them), `T` (`[160..192)`) and the block (`[192..256)`: the
32 bytes of message, then the padding, written once). So the function uses
no stack.

`vg_sha256_compress` never writes `r0` or `r3` and preserves `r4`–`r11`, so
`t` stays in `r0` and `scratch` in `r3`, and our other variables live in
`r4` (`key`) and `r5` (the steps left); `r1` and `r12` are temporaries.
-/

namespace VG.Impl.Pbkdf2.Arm

open VG.Arm
open VG.Impl.Sha256.Arm.Stream (save restore compressAt)
open VG.Impl.Hmac.Arm (cp)

/-- The padding of a 96-byte message, after 32 bytes of it, in `scratch[224..256)`:
`0x80`, zeros, and the length in bits (768), big-endian. -/
def padding : List Instr :=
  [.mov .r12 (.imm 0x80), .str .r12 .r3 224, .mov .r12 (.imm 0), .str .r12 .r3 228,
    .str .r12 .r3 232, .str .r12 .r3 236, .str .r12 .r3 240, .str .r12 .r3 244, .str .r12 .r3 248,
    .mov .r12 (.imm 0x30000), .str .r12 .r3 252]

/-- The hash value at `[r4 + o]` into `t` (at `r0`). -/
def load (o : Nat) : List Instr := (List.range 8).flatMap (cp .r12 .r4 .r0 o 0)

/-- Word `k` of the digest (the hash value's words, big-endian) into the block. -/
def outW (k : Nat) : List Instr :=
  [.ldr .r12 .r0 (4 * k), .rev .r12 .r12, .str .r12 .r3 (192 + 4 * k)]

/-- The digest into the block's first 32 bytes. -/
def digest : List Instr := (List.range 8).flatMap outW

/-- `T ← T ⊕ U` for 32-bit word `k`, with `T` in `scratch[160..192)` and `U`
the block's first 32 bytes. -/
def xorW (k : Nat) : List Instr :=
  [.ldr .r12 .r3 (160 + 4 * k), .ldr .r1 .r3 (192 + 4 * k), .dp .eor .r12 .r12 (.reg .r1),
    .str .r12 .r3 (160 + 4 * k)]

/-- Pointing `r1` at the block, for `compressAt`. -/
def atBlock : Instr := .dp .add .r1 .r3 (.imm 192)

/-- One step. -/
def body : Prog isa :=
  .seq (.block (load 0 ++ [atBlock]))
  (.seq compressAt
  (.seq (.block (digest ++ load 96 ++ [atBlock]))
  (.seq compressAt
    (.block (digest ++ (List.range 8).flatMap xorW ++ [.subs .r5 .r5 (.imm 1)])))))

/-- Saving our caller's registers and our return address, setting up our
registers, and writing `U` and the padding into the block and `T` into
`scratch`. -/
def prologue : List Instr :=
  [.ldrSp .r12 0] ++ save .r12 ++
    [.mov .r4 (.reg .r0), .mov .r0 (.reg .r3), .mov .r3 (.reg .r12), .mov .r5 (.reg .r2)] ++
    (List.range 8).flatMap (cp .r12 .r1 .r3 0 192) ++ (List.range 8).flatMap (cp .r12 .r0 .r3 0 160) ++
    padding ++ [.cmp .r5 (.imm 0)]

/-- `T` back into `t`, and restoring our return address and our caller's registers. -/
def epilogue : List Instr := (List.range 8).flatMap (cp .r12 .r3 .r0 160 0) ++ restore

def iterate : Prog isa :=
  .seq (.block prologue)
  (.seq (.ite .eq (.block []) (.loop body .ne))
    (.block epilogue))

end VG.Impl.Pbkdf2.Arm
