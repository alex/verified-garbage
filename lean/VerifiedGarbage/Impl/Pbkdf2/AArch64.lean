import VerifiedGarbage.Impl.Hmac.AArch64

/-!
# PBKDF2-HMAC-SHA-256's iteration: AArch64 implementation

`iterate(key = x0, u = x1, n = w2, t = x3, scratch = x4)` runs `n` steps
`U ← HMAC (K₀, U)`, `T ← T ⊕ U` (`VG.Spec.Pbkdf2.iterate`), for the key
whose inner and outer streaming states are at `key` and `key + 96`.

The same design as on x86-64 (`VG.Impl.Pbkdf2.X86_64`): the inner and outer
states have each absorbed one block, so HMAC-SHA-256 of the 32-byte `U` is
two compressions (calls of `vg_sha256_compress`, through the streaming
code's `compressAt`), each of one block that is 32 bytes of message followed
by the padding of a 96-byte message.

`scratch` holds the compression's scratch space (`[0..112)`), our caller's
`x19`–`x24` (`[112..160)`, where the streaming code's `save` and `restore`
keep them), the hash value being compressed (`[160..192)`), the block
(`[192..256)`: the 32 bytes of message, then the padding, written once) and
our return address `x30` (`[256..264)`), which each call replaces. So the
function uses no stack. `vg_sha256_compress` preserves `x19`–`x28`, so our
variables live there: `x19` = the hash value being compressed, `x20` =
`scratch`, `x21` = `key`, `x22` = `t` and `x23` = the steps left.

`n` is a 32-bit argument, whose register's upper half is whatever the caller
left there (possibly secret): the first instruction zero-extends it.
-/

namespace VG.Impl.Pbkdf2.AArch64

open VG.AArch64
open VG.Impl.Sha256.AArch64.Stream (mov save restore compressAt)
open VG.Impl.Hmac.AArch64 (cp64)

/-- The padding of a 96-byte message, after 32 bytes of it, in `scratch[224..256)`:
`0x80`, zeros, and the length in bits (768), big-endian. -/
def padding : List Instr :=
  [.movz .x .x9 0x80 0, .str .x .x9 .x20 224, .movz .x .x9 0 0, .str .x .x9 .x20 232,
    .str .x .x9 .x20 240, .movz .x .x9 3 3, .str .x .x9 .x20 248]

/-- The hash value at `[x21 + o]` into `scratch[160..192)` (at `x19`). -/
def load (o : Nat) : List Instr := (List.range 4).flatMap (cp64 .x21 .x19 o 0)

/-- Word `k` of the digest (the hash value's words, big-endian) into the block. -/
def outW (k : Nat) : List Instr :=
  [.ldr .w .x9 .x19 (4 * k), .rev32 .x9 .x9, .str .w .x9 .x20 (192 + 4 * k)]

/-- The digest into the block's first 32 bytes. -/
def digest : List Instr := (List.range 8).flatMap outW

/-- `T ← T ⊕ U` for 64-bit word `k`, with `U` the block's first 32 bytes. -/
def xorW (k : Nat) : List Instr :=
  [.ldr .x .x9 .x20 (192 + 8 * k), .ldr .x .x10 .x22 (8 * k), .logic .eor .x .x9 .x9 .x10,
    .str .x .x9 .x22 (8 * k)]

/-- Pointing `x1` at the block, for `compressAt`. -/
def atBlock : Instr := .addImm .x .x1 .x20 192

/-- One step. -/
def body : Prog isa :=
  .seq (.block (load 0 ++ [atBlock]))
  (.seq compressAt
  (.seq (.block (digest ++ load 96 ++ [atBlock]))
  (.seq compressAt
    (.block (digest ++ (List.range 4).flatMap xorW ++ [.subImm .x .x23 .x23 1])))))

/-- Saving our caller's registers and our return address, setting up our
registers, and writing `U` and the padding into the block. -/
def prologue : List Instr :=
  save .x4 ++ [.str .x .x30 .x4 256, .addImm .x .x19 .x4 160, mov .x20 .x4, mov .x21 .x0,
    mov .x22 .x3, mov .x23 .x2] ++ (List.range 4).flatMap (cp64 .x1 .x20 0 192) ++ padding

/-- Restoring our return address and our caller's registers. -/
def epilogue : List Instr := .ldr .x .x30 .x20 256 :: restore

/-- `iterate`, once `n` is zero-extended. -/
def main : Prog isa :=
  .seq (.block prologue)
  (.seq (.ite (.zero .x .x23) (.block []) (.loop body (.nonzero .x .x23)))
    (.block epilogue))

def iterate : Prog isa := .seq (.block [.addImm .w .x2 .x2 0]) main

end VG.Impl.Pbkdf2.AArch64
