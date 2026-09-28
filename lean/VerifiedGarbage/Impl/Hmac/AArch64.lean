import VerifiedGarbage.Impl.Sha256.AArch64.Stream

/-!
# HMAC-SHA-256: AArch64 implementation

The same algorithm as on x86-64 (`VG.Impl.Hmac.X86_64`): two SHA-256
streaming states (`inner`, `outer`; see `VG.Spec.Hmac`).

* `init(inner = x0, outer = x1, key = x2, key_len = x3, scratch = x4)`
  stores `H⁽⁰⁾` in both states, the block `K₀ ⊕ ipad` in the inner buffer
  and `K₀ ⊕ opad` in the outer one, and compresses both (calling
  `vg_sha256_compress`).
* `finalize(inner = x0, outer = x1, count = x2, scratch = x3)` finalizes the
  inner state (calling `vg_sha256_finalize`), makes the inner state
  represent `(K₀ ⊕ opad) ‖ digest` (96 bytes) from the outer hash value and
  that digest, and finalizes it again, leaving the MAC in
  `scratch[176..208)`.
-/

namespace VG.Impl.Hmac.AArch64

open VG.AArch64
open VG.Impl.Sha256.AArch64.Stream (mov compressAt save restore)

/-! ## `init`

As in the streaming SHA-256 `update`, the call of the compression function
(`compressAt`: the block at `x1` into the hash value at `x19`, with scratch
space `x20`) preserves `x19`–`x28`, so our variables live in `x19`–`x24`,
our caller's values of those are saved in `scratch[112..160)`, and our return
address in a stack frame.

Registers: `x19` = the state being compressed (`inner`, then `outer`), `x20`
= `scratch`, `x21` = `outer`, `x22` = the next key byte, `x23` = key bytes
left, `x24` = the byte index, `x14` = `0x36` (`ipad`), `x15` = `0x5c`
(`opad`). Byte `x24` of a buffer is addressed as `[x12, #32]` with
`x12 = state + x24`. -/

/-- `H⁽⁰⁾` into the state at `b`. -/
def h0 (b : Reg) : List Instr :=
  (List.range 8).flatMap fun k =>
    [.movz .w .x9 (Spec.Sha256.H0[k]!.extractLsb' 0 16) 0,
     .movk .w .x9 (Spec.Sha256.H0[k]!.extractLsb' 16 16) 1,
     .str .w .x9 b (4 * k)]

/-- The key bytes, XORed with `ipad` into the inner buffer and `opad` into the outer one. -/
def keyLoop : Prog isa :=
  .loop (.block [.ldrb .x9 .x22 0,
    .logic .eor .x .x10 .x9 .x14, .add .x .x12 .x19 .x24, .strb .x10 .x12 32,
    .logic .eor .x .x10 .x9 .x15, .add .x .x12 .x21 .x24, .strb .x10 .x12 32,
    .addImm .x .x22 .x22 1, .addImm .x .x24 .x24 1, .subImm .x .x23 .x23 1]) (.nonzero .x .x23)

/-- The zero bytes after the key (`x11` of them), XORed likewise. -/
def padLoop : Prog isa :=
  .loop (.block [.add .x .x12 .x19 .x24, .strb .x14 .x12 32, .add .x .x12 .x21 .x24, .strb .x15 .x12 32,
    .addImm .x .x24 .x24 1, .subImm .x .x11 .x11 1]) (.nonzero .x .x11)

/-- `init`, but for saving `x30`. -/
def initMain : Prog isa :=
  .seq (.block (save .x4 ++ [mov .x19 .x0, mov .x20 .x4, mov .x21 .x1, mov .x22 .x2, mov .x23 .x3] ++
      h0 .x19 ++ h0 .x21 ++ [.movz .x .x14 0x36 0, .movz .x .x15 0x5c 0, .movz .x .x24 0 0]))
  (.seq (.ite (.zero .x .x23) (.block []) keyLoop)
  (.seq (.block [.movz .x .x11 64 0, .sub .x .x11 .x11 .x24])
  (.seq (.ite (.zero .x .x11) (.block []) padLoop)
  (.seq (.block [.addImm .x .x1 .x19 32])
  (.seq compressAt
  (.seq (.block [mov .x19 .x21, .addImm .x .x1 .x19 32])
  (.seq compressAt
    (.block restore))))))))

def init : Prog isa := .frame (.push .x30) initMain (.pop .x30)

/-! ## `finalize`

The MAC is left in `scratch[176..208)`. The outer hash value is first copied
to `scratch[208..240)`; the inner state is finalized into
`scratch[176..208)`; then the inner state is overwritten with the outer hash
value and that digest, so that it represents `(K₀ ⊕ opad) ‖ digest`, and
finalized again.

`inner` and `scratch` are kept in `x25` and `x26`, which the calls of
`vg_sha256_finalize` preserve and never even write (so the taint analysis
knows they are still public after them); our caller's values of those are
saved in `scratch[160..176)`, and our return address in a stack frame. -/

/-- Copying 32-bit word `k` from `[src + o₁]` to `[dst + o₂]`. -/
def cp32 (src dst : Reg) (o₁ o₂ k : Nat) : List Instr :=
  [.ldr .w .x9 src (o₁ + 4 * k), .str .w .x9 dst (o₂ + 4 * k)]

/-- Copying 64-bit word `k` from `[src + o₁]` to `[dst + o₂]`. -/
def cp64 (src dst : Reg) (o₁ o₂ k : Nat) : List Instr :=
  [.ldr .x .x9 src (o₁ + 8 * k), .str .x .x9 dst (o₂ + 8 * k)]

/-- The outer hash value into `scratch[208..240)`. -/
def saveOuter : List Instr := (List.range 8).flatMap (cp32 .x1 .x3 0 208)

/-- The outer hash value and the first digest into the inner state. -/
def loadOuter : List Instr :=
  (List.range 8).flatMap (cp32 .x26 .x25 208 0) ++ (List.range 4).flatMap (cp64 .x26 .x25 176 32)

/-- A call of `vg_sha256_finalize`. -/
def sha256Finalize : Prog isa := .call "vg_sha256_finalize" Impl.Sha256.AArch64.Stream.finalize

/-- `finalize`, but for saving `x30`. -/
def finalizeMain : Prog isa :=
  .seq (.block ([.str .x .x25 .x3 160, .str .x .x26 .x3 168, mov .x25 .x0, mov .x26 .x3] ++ saveOuter ++
      [mov .x1 .x2, .addImm .x .x2 .x3 176]))
  (.seq sha256Finalize
  (.seq (.block (loadOuter ++ [mov .x0 .x25, .movz .x .x1 96 0, .addImm .x .x2 .x26 176, mov .x3 .x26]))
  (.seq sha256Finalize
    (.block [.ldr .x .x25 .x26 160, .ldr .x .x26 .x26 168]))))

def finalize : Prog isa := .frame (.push .x30) finalizeMain (.pop .x30)

end VG.Impl.Hmac.AArch64
