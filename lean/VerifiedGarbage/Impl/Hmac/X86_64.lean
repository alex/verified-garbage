import VerifiedGarbage.Impl.Sha256.X86_64.Stream

/-!
# HMAC-SHA-256: x86-64 implementation

Two SHA-256 streaming states (`inner`, `outer`; see `VG.Spec.Hmac`).

* `init(inner = rdi, outer = rsi, key = rdx, key_len = rcx, scratch = r8)`
  stores `H⁽⁰⁾` in both states, the block `K₀ ⊕ ipad` in the inner buffer
  and `K₀ ⊕ opad` in the outer one, and compresses both (calling a
  compression function, e.g. `vg_sha256_compress`).
* `finalize(inner = rdi, outer = rsi, count = rdx, scratch = rcx)`
  finalizes the inner state (calling a SHA-256 finalization, e.g.
  `vg_sha256_finalize`), makes the inner state represent
  `(K₀ ⊕ opad) ‖ digest` (96 bytes) from the outer hash value and that
  digest, and finalizes it again, leaving the MAC in `scratch[176..208)`.

Both take the compression function they call, directly or through the
finalization (a `Callee`), and are emitted once for each implementation
(`Generic/Sha256Compress/X86_64/Hmac.lean`).

As in the streaming SHA-256 functions, the functions we call preserve `rbx,
rbp, r12–r15`, so our variables live there; our caller's are saved in
`scratch` beyond what the called functions use.
-/

namespace VG.Impl.Hmac.X86_64

open VG.X86_64
open VG.Impl.Sha256.X86_64 (at_)
open VG.Impl.Sha256.X86_64.Stream (Callee compressAt restore)

/-! ## `init`

Registers: `rbx` = `inner`, `r12` = `outer`, `r15` = `scratch`, `rbp` =
`key`, `r13` = `key_len`, `r14` = the byte index. -/

/-- `[b + r14 + 32]`: byte `r14` of a state's buffer. -/
def bufAt (b : Reg) : MemOp := { base := b, index := some .r14, scale := 1, disp := 32 }

/-- `H⁽⁰⁾` into the state at `b`. -/
def h0 (b : Reg) : List Instr :=
  (List.range 8).flatMap fun k => [.mov32 .rax (.imm Spec.Sha256.H0[k]!), .store32 (at_ b (4 * k)) .rax]

/-- The key bytes, XORed with `ipad` into the inner buffer and `opad` into the outer one. -/
def keyLoop : Prog isa :=
  .loop (.block [.movzx8 .rax { base := .rbp, index := some .r14, scale := 1 }, .mov32 .rcx (.reg .rax),
    .alu32 .xor .rax (.imm 0x36), .store8 (bufAt .rbx) .rax, .alu32 .xor .rcx (.imm 0x5c),
    .store8 (bufAt .r12) .rcx, .alu .add .r14 (.imm 1), .alu .cmp .r14 (.reg .r13)]) .ne

/-- The zero bytes after the key, XORed likewise. -/
def padLoop : Prog isa :=
  .loop (.block [.store8 (bufAt .rbx) .rax, .store8 (bufAt .r12) .rcx, .alu .add .r14 (.imm 1),
    .alu .cmp .r14 (.imm 64)]) .ne

/-- Everything before the first compression: the two hash values, the two
key blocks, and `rsi` pointing at the inner one. -/
def initKeys : Prog isa :=
  .seq (.block (Impl.Sha256.X86_64.Stream.save .r8 ++ [.mov .rbx (.reg .rdi), .mov .r12 (.reg .rsi), .mov .r15 (.reg .r8),
      .mov .rbp (.reg .rdx), .mov .r13 (.reg .rcx)] ++ h0 .rbx ++ h0 .r12 ++
      [.mov32 .r14 (.imm 0), .alu .test .r13 (.reg .r13)]))
  (.seq (.ite .e (.block []) keyLoop)
  (.seq (.block [.mov32 .rax (.imm 0x36), .mov32 .rcx (.imm 0x5c), .alu .cmp .r14 (.imm 64)])
  (.seq (.ite .e (.block []) padLoop)
    (.block [.mov .rsi (.reg .rbx), .alu .add .rsi (.imm 32)]))))

/-- `init`, calling the compression function `f`. -/
def init (f : Callee) : Prog isa :=
  .seq initKeys
  (.seq (compressAt f)
  (.seq (.block [.mov .rbx (.reg .r12), .mov .rsi (.reg .r12), .alu .add .rsi (.imm 32)])
  (.seq (compressAt f)
    (.block restore))))

/-! ## `finalize`

`finalize(inner = rdi, outer = rsi, count = rdx, scratch = rcx)`: the MAC is
left in `scratch[176..208)`. The outer hash value is first copied to
`scratch[640..672)`; the inner state is finalized into `scratch[608..640)`,
with `scratch[0..608)` as the finalization's scratch space; then the inner
state is overwritten with the outer hash value and that digest, so that it
represents `(K₀ ⊕ opad) ‖ digest`, and finalized again, into
`scratch[608..640)` too, from where the MAC is copied to `scratch[176..208)`.
Everything after the first finalization is addressed through `rdi` (the
state) and `rcx` (the scratch space), the only registers the called
finalization leaves pointing at their regions, which constant time needs;
and we use no callee-saved register ourselves. -/

/-- Copying 32-bit word `k` from `[src + o₁]` to `[dst + o₂]`. -/
def cp32 (src dst : Reg) (o₁ o₂ k : Nat) : List Instr :=
  [.mov32 .rax (.mem (at_ src (o₁ + 4 * k))), .store32 (at_ dst (o₂ + 4 * k)) .rax]

/-- Copying 64-bit word `k` from `[src + o₁]` to `[dst + o₂]`. -/
def cp64 (src dst : Reg) (o₁ o₂ k : Nat) : List Instr :=
  [.mov .rax (.mem (at_ src (o₁ + 8 * k))), .store (at_ dst (o₂ + 8 * k)) .rax]

/-- The outer hash value into `scratch[640..672)`. -/
def saveOuter : List Instr := (List.range 8).flatMap (cp32 .rsi .rcx 0 640)

/-- The outer hash value and the first digest into the inner state. -/
def loadOuter : List Instr :=
  (List.range 8).flatMap (cp32 .rcx .rdi 640 0) ++ (List.range 4).flatMap (cp64 .rcx .rdi 608 32)

/-- The MAC from `scratch[608..640)` into `scratch[176..208)`. -/
def storeMac : List Instr := (List.range 4).flatMap (cp64 .rcx .rcx 608 176)

/-- The streaming SHA-256 finalization calling `f`, whose symbol is `name`
(`vg_sha256_finalize` for the scalar compression function). -/
def sha256Finalize (f : Callee) (name : String) : Prog isa :=
  .call name (Impl.Sha256.X86_64.Stream.finalize f)

/-- `finalize`, calling the SHA-256 finalization `name`, which calls the
compression function `f`. -/
def finalize (f : Callee) (name : String) : Prog isa :=
  .seq (.block (saveOuter ++ [.mov .rsi (.reg .rdx), .mov .rdx (.reg .rcx), .alu .add .rdx (.imm 608)]))
  (.seq (sha256Finalize f name)
  (.seq (.block (loadOuter ++ [.mov32 .rsi (.imm 96), .mov .rdx (.reg .rcx), .alu .add .rdx (.imm 608)]))
  (.seq (sha256Finalize f name)
    (.block storeMac))))

end VG.Impl.Hmac.X86_64
