import VerifiedGarbage.Impl.Hmac.X86_64

/-!
# PBKDF2-HMAC-SHA-256's iteration: x86-64 implementation

`iterate(key = rdi, u = rsi, n = edx, t = rcx, scratch = r8)` runs `n` steps
`U ← HMAC (K₀, U)`, `T ← T ⊕ U` (`VG.Spec.Pbkdf2.iterate`), for the key
whose inner and outer streaming states are at `key` and `key + 96`.

The inner and outer states have each absorbed one block, so HMAC-SHA-256 of
the 32-byte `U` is two compressions (calls of a compression function `f`,
e.g. `vg_sha256_compress` or `vg_sha256_compress_shani`), each of
one block that is 32 bytes of message followed by the padding of a 96-byte
message: the inner hash value with the block `U ‖ pad`, then the outer hash
value with the block `digest ‖ pad`.

`scratch` holds the compression's scratch space (`[0..560)`), the hash value
being compressed (`[560..592)`), the block (`[592..656)`: the 32 bytes of
message, then the padding, written once) and our caller's registers
(`[656..680)`). `f` never writes `rdi` (the hash value) or `rcx` (its
scratch space), so those stay put, and it preserves `rbx` = `key`, `rbp` =
`t` and `r13` = the steps left.
-/

namespace VG.Impl.Pbkdf2.X86_64

open VG.X86_64
open VG.Impl.Sha256.X86_64 (at_)
open VG.Impl.Sha256.X86_64.Stream (Callee)
open VG.Impl.Hmac.X86_64 (cp64)

/-- The callee-saved registers we use, and where they are saved in `scratch`. -/
def saved : List (Reg × Nat) := [(.rbx, 656), (.rbp, 664), (.r13, 672)]

/-- The padding of a 96-byte message, after 32 bytes of it, in `scratch[624..656)`:
`0x80`, zeros, and the length in bits (768), big-endian. -/
def padding : List Instr :=
  [.mov32 .rax (.imm 0x80), .store (at_ .rcx 624) .rax, .mov32 .rax (.imm 0), .store (at_ .rcx 632) .rax,
    .store (at_ .rcx 640) .rax, .store32 (at_ .rcx 648) .rax, .mov32 .rax (.imm 0x30000),
    .store32 (at_ .rcx 652) .rax]

/-- The hash value at `[rbx + o]` into `scratch[560..592)`. -/
def load (o : Nat) : List Instr := (List.range 4).flatMap (cp64 .rbx .rdi o 0)

/-- Word `k` of the digest (the hash value's words, big-endian) into the block. -/
def outW (k : Nat) : List Instr :=
  [.mov32 .rax (.mem (at_ .rdi (4 * k))), .bswap32 .rax, .store32 (at_ .rcx (592 + 4 * k)) .rax]

/-- The digest into the block's first 32 bytes. -/
def digest : List Instr := (List.range 8).flatMap outW

/-- `T ← T ⊕ U` for 64-bit word `k`, with `U` the block's first 32 bytes. -/
def xorW (k : Nat) : List Instr :=
  [.mov .rax (.mem (at_ .rcx (592 + 8 * k))), .alu .xor .rax (.mem (at_ .rbp (8 * k))),
    .store (at_ .rbp (8 * k)) .rax]

/-- A call of the compression function `f` on the block. -/
def compressBlock (f : Callee) : Prog isa :=
  .seq (.block [.mov .rsi (.reg .rcx), .alu .add .rsi (.imm 592), .mov32 .rdx (.imm 1)])
    (.call f.name f.code)

/-- One step. -/
def body (f : Callee) : Prog isa :=
  .seq (.block (load 0))
  (.seq (compressBlock f)
  (.seq (.block (digest ++ load 96))
  (.seq (compressBlock f)
    (.block (digest ++ (List.range 4).flatMap xorW ++ [.alu .sub .r13 (.imm 1)])))))

/-- Saving our caller's registers, setting up ours, and writing `U` and the
padding into the block. -/
def prologue : List Instr :=
  saved.map (fun (r, d) => .store (at_ .r8 d) r) ++
    [.mov32 .r13 (.reg .rdx), .mov .rbx (.reg .rdi), .mov .rbp (.reg .rcx), .mov .rcx (.reg .r8),
      .mov .rdi (.reg .r8), .alu .add .rdi (.imm 560)] ++
    (List.range 4).flatMap (cp64 .rsi .rcx 0 592) ++ padding ++ [.alu .test .r13 (.reg .r13)]

/-- Restoring our caller's registers. -/
def epilogue : List Instr := saved.map fun (r, d) => .mov r (.mem (at_ .rcx d))

def iterate (f : Callee) : Prog isa :=
  .seq (.block prologue) (.seq (.ite .e (.block []) (.loop (body f) .ne)) (.block epilogue))

end VG.Impl.Pbkdf2.X86_64
