import VerifiedGarbage.Impl.MdStream.AArch64

/-!
# PBKDF2-HMAC's iteration over a Merkle–Damgård hash function: AArch64 implementation

`iterate(key = x0, u = x1, n = w2, t = x3, scratch = x4)` runs `n` steps
`U ← HMAC (K₀, U)`, `T ← T ⊕ U` (`VG.Spec.Pbkdf2.iterate`), for the key
whose inner and outer streaming states are at `key` and `key + N + B`.

The same design as on x86-64 (`Impl/Pbkdf2/X86_64.lean`): it serves every
Merkle–Damgård hash function (MD5, SHA-1, SHA-256 and the SHA-512 family),
from the sizes of its hash value, block and length field, its length field's
and digest's code (`Params`) and its compression function (`name`, `code`),
with `D` the size of the digest.

The inner and outer states have each absorbed one block, so HMAC of the
`D`-byte `U` is two compressions, each of one block that is `D` bytes of
message followed by the padding of a `B + D`-byte message: the inner hash
value with the block `U ‖ pad`, then the outer hash value with the block
`digest ‖ pad`. The padding is written once, before the loop; the digest's
`N - D` bytes past `D` (for a truncated hash function), which overwrite its
start, are written back after each.

`scratch` holds the compression function's scratch space (`[0..so)`), our
caller's `x19`–`x24` (`[so..so+48)`, where the streaming code's `save` and
`restore` keep them), our return address `x30` (`[so+48..so+56)`), which
each call replaces, the hash value being compressed (`N` bytes from
`so + 56`) and right after it the block (`B` bytes). So the function uses
no stack. The compression function preserves `x19`–`x28`, so our variables
live there: `x19` = the hash value, `x20` = `scratch`, `x21` = the block,
`x22` = `key` (the byte count of the length field before the loop), `x23` =
`t` and `x24` = the steps left. Every address and branch depends only on the
pointers and `n`.

`n` is a 32-bit argument, whose register's upper half is whatever the caller
left there (possibly secret): the first instruction zero-extends it.
-/

namespace VG.Impl.Pbkdf2.AArch64

open VG.AArch64
open VG.Impl.MdStream.AArch64 (mov save restore compressAt)

/-- What PBKDF2's iteration needs of a Merkle–Damgård hash function's code. -/
structure Params where
  /-- The size of the hash value. -/
  N : Nat
  /-- The size of a block. -/
  B : Nat
  /-- The size of the length field. -/
  L : Nat
  /-- The size of the compression function's scratch space. -/
  so : Nat
  /-- Stores the length field, from the byte count in `x22`, at
  `x19 + N + B - L`; writes only `x9` and `x12`. -/
  len : List Instr
  /-- Writes the digest, from the hash value at `x19`, to `x21`; writes only
  `x9`. -/
  out : List Instr

namespace Params

variable (P : Params)

/-- The streaming code's parameters with the same hash value, scratch space,
length field and digest, whose `save`, `restore` and `compressAt` we use. -/
def md : MdStream.AArch64.Params := ⟨P.N, P.so, P.len, P.out⟩

end Params

/-- The streaming code's parameters of a hash function with 64-byte blocks
and an 8-byte length field (MD5, SHA-1, SHA-256), as the iteration's. -/
def ofMd (P : MdStream.AArch64.Params) : Params := ⟨P.N, 64, 8, P.so, P.len, P.out⟩

/-- Copying 32-bit word `k` from `[src + o₁]` to `[dst + o₂]`. -/
def cp32 (src dst : Reg) (o₁ o₂ k : Nat) : List Instr :=
  [.ldr .w .x9 src (o₁ + 4 * k), .str .w .x9 dst (o₂ + 4 * k)]

/-- The `n` 64-bit words at `x19`, written to `x21`, big-endian: the digest of
the SHA-512 family. -/
def out64 (n : Nat) : List Instr :=
  (List.range n).flatMap fun k => [.ldr .x .x9 .x19 (8 * k), .rev .x9 .x9, .str .x .x9 .x21 (8 * k)]

/-- The 16-byte length in bits, `8 · count` (from `count` in `x22`), big-endian
at `x19 + d`: the length field of the SHA-512 family. `d` is a multiple of 8. -/
def len128 (d : Nat) : List Instr :=
  [.lsr .x .x9 .x22 61, .rev .x9 .x9, .str .x .x9 .x19 d] ++ MdStream.AArch64.len64 (d + 8) true

/-- The SHA-512 family's: a 64-byte hash value, 128-byte blocks, a 16-byte
length field and the 176 bytes of scratch space of `vg_sha512_compress`. -/
def sha512 : Params := ⟨64, 128, 16, 176, len128 176, out64 8⟩

variable (P : Params) (D : Nat)

/-- Where our return address is saved in `scratch`. -/
def raO : Nat := P.so + 48

/-- Where the hash value being compressed is in `scratch`. -/
def hvO : Nat := P.so + 56

/-- Where the block is. -/
def blkO : Nat := P.so + 56 + P.N

/-- The hash value at `key + o` into `[x19]`. -/
def loadKey (o : Nat) : List Instr := (List.range (P.N / 4)).flatMap (cp32 .x22 .x19 o 0)

/-- `0x80` then zeros in the block, from byte `a` up to byte `b` (`a < b`,
both multiples of 4). -/
def padFrom (a b : Nat) : List Instr :=
  [.movz .x .x9 0x80 0, .str .w .x9 .x21 a, .movz .x .x9 0 0] ++
    (List.range ((b - a) / 4 - 1)).map fun k => .str .w .x9 .x21 (a + 4 + 4 * k)

/-- The digest of the hash value into the block, and the padding it
overwrote written back. -/
def digest : List Instr := P.out ++ (if D < P.N then padFrom D P.N else [])

/-- `T ← T ⊕ U` for 32-bit word `k`, with `U` the block's first `D` bytes. -/
def xorW (k : Nat) : List Instr :=
  [.ldr .w .x9 .x21 (4 * k), .ldr .w .x10 .x23 (4 * k), .logic .eor .x .x9 .x9 .x10,
    .str .w .x9 .x23 (4 * k)]

/-- One compression of the block into the hash value. -/
def compressBlock (name : String) (code : Prog isa) : Prog isa :=
  .seq (.block [mov .x1 .x21]) (compressAt name code)

/-- One step. -/
def body (name : String) (code : Prog isa) : Prog isa :=
  .seq (.block (loadKey P 0))
  (.seq (compressBlock name code)
  (.seq (.block (digest P D ++ loadKey P (P.N + P.B)))
  (.seq (compressBlock name code)
    (.block (digest P D ++ (List.range (D / 4)).flatMap xorW ++ [.subImm .x .x24 .x24 1])))))

/-- Saving our caller's registers and our return address, setting up our
registers, and writing `U` and the padding into the block: `0x80`, zeros,
and the length field of a `B + D`-byte message, which `P.len` stores from
`x22` at `x19 + N + B - L`, the end of the block. -/
def prologue : List Instr :=
  save P.md .x4 ++
    [.str .x .x30 .x4 (raO P), .addImm .x .x19 .x4 (hvO P), mov .x20 .x4,
      .addImm .x .x21 .x4 (blkO P), mov .x23 .x3, mov .x24 .x2] ++
    (List.range (D / 4)).flatMap (cp32 .x1 .x21 0 0) ++ padFrom D (P.B - P.L) ++
    [.movz .x .x22 (BitVec.ofNat 16 (P.B + D)) 0] ++ P.len ++ [mov .x22 .x0]

/-- Restoring our return address and our caller's registers. -/
def epilogue : List Instr := .ldr .x .x30 .x20 (raO P) :: restore P.md

/-- `iterate`, once `n` is zero-extended. -/
def main (name : String) (code : Prog isa) : Prog isa :=
  .seq (.block (prologue P D))
  (.seq (.ite (.zero .x .x24) (.block []) (.loop (body P D name code) (.nonzero .x .x24)))
    (.block (epilogue P)))

def iterate (name : String) (code : Prog isa) : Prog isa :=
  .seq (.block [.addImm .w .x2 .x2 0]) (main P D name code)

end VG.Impl.Pbkdf2.AArch64
