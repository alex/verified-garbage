import VerifiedGarbage.Impl.MdStream.X86_64
import VerifiedGarbage.Impl.Hmac.X86_64

/-!
# PBKDF2-HMAC's iteration over a Merkle–Damgård hash function: x86-64 implementation

`iterate(key = rdi, u = rsi, n = edx, t = rcx, scratch = r8)` runs `n` steps
`U ← HMAC (K₀, U)`, `T ← T ⊕ U` (`VG.Spec.Pbkdf2.iterate`), for the key
whose inner and outer streaming states are at `key` and `key + N + B`.

It serves every hash function whose streaming code is the generic one of
`Impl/MdStream/X86_64.lean` (MD5, SHA-1, SHA-256 and the SHA-512 family),
from the same `Params` and compression function (`name`, `code`), with
`D` the size of the digest.

The inner and outer states have each absorbed one block, so HMAC of the
`D`-byte `U` is two compressions, each of one block that is `D` bytes of
message followed by the padding of a `B + D`-byte message: the inner hash
value with the block `U ‖ pad`, then the outer hash value with the block
`digest ‖ pad`. The padding is written once, before the loop; the digest's
`N - D` bytes past `D` (for a truncated hash function), which overwrite its
start, are written back after each.

`scratch` holds the compression function's scratch space (`[0..so)`), our
caller's registers (`[so..so+48)`), the hash value being compressed (`N`
bytes from `so + 48`) and right after it the block (`B` bytes). Registers:
`rbx` = the hash value, `rbp` = the block, `r12` = `key`, `r13` = `t`,
`r14` = the steps left, `r15` = `scratch`; the compression function
preserves them. Every address and branch depends only on the pointers and
`n`.
-/

namespace VG.Impl.Pbkdf2.X86_64

open VG.X86_64
open VG.Impl.MdStream.X86_64 (Params at_ save restore compressAt)
open VG.Impl.Hmac.X86_64 (cp32)

variable (P : Params) (D : Nat)

/-- Where the hash value being compressed is in `scratch`. -/
def hvO : Nat := P.so + 48

/-- Where the block is. -/
def blkO : Nat := P.so + 48 + P.N

/-- The hash value at `key + o` into `[rbx]`. -/
def loadKey (o : Nat) : List Instr := (List.range (P.N / 4)).flatMap (cp32 .r12 .rbx o 0)

/-- `0x80` then zeros in the block, from byte `a` up to byte `b` (`a < b`,
both multiples of 4). -/
def padFrom (a b : Nat) : List Instr :=
  [.mov32 .rax (.imm 0x80), .store32 (at_ .rbp a) .rax, .mov32 .rax (.imm 0)] ++
    (List.range ((b - a) / 4 - 1)).map fun k => .store32 (at_ .rbp (a + 4 + 4 * k)) .rax

/-- The digest of the hash value into the block, and the padding it
overwrote written back. -/
def digest : List Instr := P.out ++ (if D < P.N then padFrom D P.N else [])

/-- `T ← T ⊕ U` for 32-bit word `k`, with `U` the block's first `D` bytes. -/
def xorW (k : Nat) : List Instr :=
  [.mov32 .rax (.mem (at_ .rbp (4 * k))), .alu32 .xor .rax (.mem (at_ .r13 (4 * k))),
    .store32 (at_ .r13 (4 * k)) .rax]

/-- One compression of the block into the hash value. -/
def compressBlock (name : String) (code : Prog isa) : Prog isa :=
  .seq (.block [.mov .rsi (.reg .rbp)]) (compressAt name code)

/-- One step. -/
def body (name : String) (code : Prog isa) : Prog isa :=
  .seq (.block (loadKey P 0))
  (.seq (compressBlock name code)
  (.seq (.block (digest P D ++ loadKey P (P.N + P.B)))
  (.seq (compressBlock name code)
    (.block (digest P D ++ (List.range (D / 4)).flatMap xorW ++ [.alu .sub .r14 (.imm 1)])))))

/-- Saving our caller's registers, setting up ours, and writing `U` and the
padding into the block: `0x80`, zeros, and the length field of a
`B + D`-byte message, which `P.len` stores from `r12` at `rbx + N + B - L`,
the end of the block. -/
def prologue : List Instr :=
  save P .r8 ++
    [.mov .r15 (.reg .r8), .mov .r12 (.reg .rdi), .mov .r13 (.reg .rcx), .mov32 .r14 (.reg .rdx),
      .mov .rbx (.reg .r8), .alu .add .rbx (.imm (BitVec.ofNat 32 (hvO P))),
      .mov .rbp (.reg .r8), .alu .add .rbp (.imm (BitVec.ofNat 32 (blkO P)))] ++
    (List.range (D / 4)).flatMap (cp32 .rsi .rbp 0 0) ++ padFrom D (P.B - P.L) ++
    [.mov32 .r12 (.imm (BitVec.ofNat 32 (P.B + D)))] ++ P.len ++
    [.mov .r12 (.reg .rdi), .alu .test .r14 (.reg .r14)]

def iterate (name : String) (code : Prog isa) : Prog isa :=
  .seq (.block (prologue P D))
    (.seq (.ite .e (.block []) (.loop (body P D name code) .ne)) (.block (restore P)))

end VG.Impl.Pbkdf2.X86_64
