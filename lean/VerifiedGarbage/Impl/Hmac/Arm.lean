import VerifiedGarbage.Impl.Sha256.Arm.Stream

/-!
# HMAC-SHA-256: 32-bit ARM implementation

The same algorithm as on x86-64 and AArch64 (`VG.Impl.Hmac.X86_64`,
`VG.Impl.Hmac.AArch64`): two SHA-256 streaming states (`inner`, `outer`; see
`VG.Spec.Hmac`).

* `init(inner = r0, outer = r1, key = r2, key_len = r3, scratch = [sp])`
  stores `H⁽⁰⁾` in both states, the block `K₀ ⊕ ipad` in the inner buffer
  and `K₀ ⊕ opad` in the outer one, and compresses both.
* `finalize(inner = r0, outer = r1, count = r2:r3, out = [sp],
  scratch = [sp, #4])` finalizes the inner state (the inlined
  `vg_sha256_finalize`, whose stack arguments are ours), writing the inner
  digest to `out`; makes the inner state represent `(K₀ ⊕ opad) ‖ digest`
  (96 bytes) from the outer hash value and that digest; and finalizes it
  again, writing the MAC to `out`.
-/

namespace VG.Impl.Hmac.Arm

open VG.Arm
open VG.Impl.Sha256.Arm.Stream (compressAt save restore)

/-! ## `init`

As in the streaming SHA-256 `update`, the blocks are compressed by calling
`vg_sha256_compress` (`compressAt`: the block at `r1` into the hash value at
`r0`, with scratch space `r3`), which preserves `r4`–`r11` and never writes
`r0` or `r3`, so our variables live in `r4`–`r9`, and our caller's
`r4`–`r11` and our return address are saved in `scratch[112..148)`
(`Impl.Sha256.Arm.Stream.save`).

Registers: `r0` = `inner` (then `outer`, for the second compression), `r4` =
`outer`, `r5` = the next key byte, `r6` = key bytes left (then pad bytes
left), `r7` = the byte index, `r8` = `0x36` (`ipad`), `r9` = `0x5c`
(`opad`); `r1`, `r2` and `r12` are temporaries. Byte `r7` of a buffer is
addressed as `[r2, #32]` with `r2 = state + r7`. `scratch` is reloaded from
the stack into `r3` for the compressions. -/

/-- `H⁽⁰⁾` into the state at `b`. -/
def h0 (b : Reg) : List Instr :=
  (List.range 8).flatMap fun k =>
    [.movw .r12 (Spec.Sha256.H0[k]!.extractLsb' 0 16),
     .movt .r12 (Spec.Sha256.H0[k]!.extractLsb' 16 16),
     .str .r12 b (4 * k)]

/-- The key bytes, XORed with `ipad` into the inner buffer and `opad` into the outer one. -/
def keyLoop : Prog isa :=
  .loop (.block [.ldrb .r12 .r5 0,
    .dp .eor .r1 .r12 (.reg .r8), .dp .add .r2 .r0 (.reg .r7), .strb .r1 .r2 32,
    .dp .eor .r1 .r12 (.reg .r9), .dp .add .r2 .r4 (.reg .r7), .strb .r1 .r2 32,
    .dp .add .r5 .r5 (.imm 1), .dp .add .r7 .r7 (.imm 1), .subs .r6 .r6 (.imm 1)]) .ne

/-- The zero bytes after the key (`r6` of them), XORed likewise. -/
def padLoop : Prog isa :=
  .loop (.block [.dp .add .r2 .r0 (.reg .r7), .strb .r8 .r2 32, .dp .add .r2 .r4 (.reg .r7),
    .strb .r9 .r2 32, .dp .add .r7 .r7 (.imm 1), .subs .r6 .r6 (.imm 1)]) .ne

def init : Prog isa :=
  .seq (.block ([.ldrSp .r12 0] ++ save .r12 ++ [.mov .r4 (.reg .r1), .mov .r5 (.reg .r2),
      .mov .r6 (.reg .r3)] ++ h0 .r0 ++ h0 .r4 ++
      [.mov .r8 (.imm 0x36), .mov .r9 (.imm 0x5c), .mov .r7 (.imm 0), .cmp .r6 (.imm 0)]))
  (.seq (.ite .eq (.block []) keyLoop)
  (.seq (.block [.mov .r6 (.imm 64), .subs .r6 .r6 (.reg .r7)])
  (.seq (.ite .eq (.block []) padLoop)
  (.seq (.block [.ldrSp .r3 0, .dp .add .r1 .r0 (.imm 32)])
  (.seq compressAt
  (.seq (.block [.mov .r0 (.reg .r4), .dp .add .r1 .r0 (.imm 32)])
  (.seq compressAt
    (.block restore))))))))

/-! ## `finalize`

The inlined finalization (which calls `vg_sha256_compress`) never writes
`r0`, saves and restores `r4`–`r11` and `lr` itself, and only writes
`inner`, `out` and `scratch[0..160)`; we use no callee-saved register.
(Calling `vg_sha256_finalize` instead would take a stack frame for its
stack arguments, which the ARMv7 taint analysis does not support yet.) The outer hash value is first copied to
`scratch[160..192)` (with `r2`, the low word of `count`, spilled to
`scratch[192..196)` to free a temporary); after the first finalization, it
and the digest (from `out`) are copied into the inner state, so that it
represents `(K₀ ⊕ opad) ‖ digest`, and `count` is set to 96. -/

/-- Copying 32-bit word `k` from `[src + o₁]` to `[dst + o₂]`, through `t`. -/
def cp (t src dst : Reg) (o₁ o₂ k : Nat) : List Instr :=
  [.ldr t src (o₁ + 4 * k), .str t dst (o₂ + 4 * k)]

/-- The outer hash value into `scratch[160..192)`. -/
def saveOuter : List Instr :=
  [.ldrSp .r12 4, .str .r2 .r12 192] ++ (List.range 8).flatMap (cp .r2 .r1 .r12 0 160) ++
    [.ldr .r2 .r12 192]

/-- The outer hash value and the first digest into the inner state, and
`count = 96`. -/
def loadOuter : List Instr :=
  [.ldrSp .r1 4, .ldrSp .r12 0] ++ (List.range 8).flatMap (cp .r3 .r1 .r0 160 0) ++
    (List.range 8).flatMap (cp .r3 .r12 .r0 0 32) ++ [.mov .r2 (.imm 96), .mov .r3 (.imm 0)]

def finalize : Prog isa :=
  .seq (.block saveOuter)
  (.seq Impl.Sha256.Arm.Stream.finalize
  (.seq (.block loadOuter)
    Impl.Sha256.Arm.Stream.finalize))

end VG.Impl.Hmac.Arm
