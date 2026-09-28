import VerifiedGarbage.Impl.Hmac.X86_64

/-!
# PBKDF2-HMAC-SHA-256's iteration: x86-64 implementation

`iterate(key = rdi, u = rsi, n = edx, t = rcx, scratch = r8)` runs `n` steps
`U ← HMAC (K₀, U)`, `T ← T ⊕ U` (`VG.Spec.Pbkdf2.iterate`), for the key
whose inner and outer streaming states are at `key` and `key + 96`.

The inner and outer states have each absorbed one block, so HMAC-SHA-256 of
the 32-byte `U` is two compressions (calls of `vg_sha256_compress`), each of
one block that is 32 bytes of message followed by the padding of a 96-byte
message: the inner hash value with the block `U ‖ pad`, then the outer hash
value with the block `digest ‖ pad`.

`scratch` holds the compression's scratch space (`[0..112)`), the hash value
being compressed (`[112..144)`), the block (`[144..208)`: the 32 bytes of
message, then the padding, written once) and our caller's registers
(`[208..232)`). `vg_sha256_compress` never writes `rdi` (the hash value) or
`rcx` (its scratch space), so those stay put, and it preserves `rbx` =
`key`, `rbp` = `t` and `r13` = the steps left.
-/

namespace VG.Impl.Pbkdf2.X86_64

open VG.X86_64
open VG.Impl.Sha256.X86_64 (at_ compress)
open VG.Impl.Hmac.X86_64 (cp64)

/-- The callee-saved registers we use, and where they are saved in `scratch`. -/
def saved : List (Reg × Nat) := [(.rbx, 208), (.rbp, 216), (.r13, 224)]

/-- The padding of a 96-byte message, after 32 bytes of it, in `scratch[176..208)`:
`0x80`, zeros, and the length in bits (768), big-endian. -/
def padding : List Instr :=
  [.mov32 .rax (.imm 0x80), .store (at_ .rcx 176) .rax, .mov32 .rax (.imm 0), .store (at_ .rcx 184) .rax,
    .store (at_ .rcx 192) .rax, .store32 (at_ .rcx 200) .rax, .mov32 .rax (.imm 0x30000),
    .store32 (at_ .rcx 204) .rax]

/-- The hash value at `[rbx + o]` into `scratch[112..144)`. -/
def load (o : Nat) : List Instr := (List.range 4).flatMap (cp64 .rbx .rdi o 0)

/-- Word `k` of the digest (the hash value's words, big-endian) into the block. -/
def outW (k : Nat) : List Instr :=
  [.mov32 .rax (.mem (at_ .rdi (4 * k))), .bswap32 .rax, .store32 (at_ .rcx (144 + 4 * k)) .rax]

/-- The digest into the block's first 32 bytes. -/
def digest : List Instr := (List.range 8).flatMap outW

/-- `T ← T ⊕ U` for 64-bit word `k`, with `U` the block's first 32 bytes. -/
def xorW (k : Nat) : List Instr :=
  [.mov .rax (.mem (at_ .rcx (144 + 8 * k))), .alu .xor .rax (.mem (at_ .rbp (8 * k))),
    .store (at_ .rbp (8 * k)) .rax]

/-- A call of `vg_sha256_compress` on the block. -/
def compressBlock : Prog isa :=
  .seq (.block [.mov .rsi (.reg .rcx), .alu .add .rsi (.imm 144), .mov32 .rdx (.imm 1)])
    (.call "vg_sha256_compress" compress)

/-- One step. -/
def body : Prog isa :=
  .seq (.block (load 0))
  (.seq compressBlock
  (.seq (.block (digest ++ load 96))
  (.seq compressBlock
    (.block (digest ++ (List.range 4).flatMap xorW ++ [.alu .sub .r13 (.imm 1)])))))

/-- Saving our caller's registers, setting up ours, and writing `U` and the
padding into the block. -/
def prologue : List Instr :=
  saved.map (fun (r, d) => .store (at_ .r8 d) r) ++
    [.mov32 .r13 (.reg .rdx), .mov .rbx (.reg .rdi), .mov .rbp (.reg .rcx), .mov .rcx (.reg .r8),
      .mov .rdi (.reg .r8), .alu .add .rdi (.imm 112)] ++
    (List.range 4).flatMap (cp64 .rsi .rcx 0 144) ++ padding ++ [.alu .test .r13 (.reg .r13)]

/-- Restoring our caller's registers. -/
def epilogue : List Instr := saved.map fun (r, d) => .mov r (.mem (at_ .rcx d))

def iterate : Prog isa :=
  .seq (.block prologue) (.seq (.ite .e (.block []) (.loop body .ne)) (.block epilogue))

end VG.Impl.Pbkdf2.X86_64
