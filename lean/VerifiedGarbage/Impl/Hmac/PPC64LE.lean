import VerifiedGarbage.Impl.Sha256.PPC64LE.Stream

/-!
# HMAC-SHA-256: PPC64LE implementation

The same algorithm as on AArch64 (`VG.Impl.Hmac.AArch64`): two SHA-256
streaming states (`inner`, `outer`; see `VG.Spec.Hmac`).

* `init(inner = r3, outer = r4, key = r5, key_len = r6, scratch = r7)`
  stores `H⁽⁰⁾` in both states, the block `K₀ ⊕ ipad` in the inner buffer
  and `K₀ ⊕ opad` in the outer one, and compresses both (calling
  `vg_sha256_compress`).
* `finalize(inner = r3, outer = r4, count = r5, out = r6, scratch = r7)`
  finalizes the inner state (calling `vg_sha256_finalize`), makes the inner
  state represent `(K₀ ⊕ opad) ‖ digest` (96 bytes) from the outer hash value
  and that digest, and finalizes it again into `out`.

Both move the link register to `r0` and save it in a frame around the
whole function, as the streaming SHA-256 functions do.
-/

namespace VG.Impl.Hmac.PPC64LE

open VG.PPC64LE
open VG.Impl.Sha256.PPC64LE.Stream (mov compressAt save restore)

/-! ## `init`

As in the streaming SHA-256 `update`, the call of the compression function
(`compressAt`: the block at `r4` into the hash value at `r26`, with scratch
space `r27`) preserves `r14`–`r31`, so our variables live in `r26`–`r31`,
and our caller's values of those are saved in `scratch[112..160)`.

Registers: `r26` = the state being compressed (`inner`, then `outer`), `r27`
= `scratch`, `r28` = `outer`, `r29` = the next key byte, `r30` = key bytes
left, `r31` = the byte index, `r12` = `0x36` (`ipad`), `r0` = `0x5c`
(`opad`). Byte `r31` of a buffer is addressed as `32(r11)` with
`r11 = state + r31`. -/

/-- `H⁽⁰⁾` into the state at `b`. -/
def h0 (b : Reg) : List Instr :=
  (List.range 8).flatMap fun k =>
    [.lis .r8 (Spec.Sha256.H0[k]!.extractLsb' 16 16),
     .ori .r8 .r8 (Spec.Sha256.H0[k]!.extractLsb' 0 16),
     .store .w .r8 b (4 * k)]

/-- The key bytes, XORed with `ipad` into the inner buffer and `opad` into the outer one. -/
def keyLoop : Prog isa :=
  .loop (.block [.lbz .r8 .r29 0,
    .logic .xor .r9 .r8 .r12, .add .r11 .r26 .r31, .stb .r9 .r11 32,
    .logic .xor .r9 .r8 .r0, .add .r11 .r28 .r31, .stb .r9 .r11 32,
    .addi .r29 .r29 1, .addi .r31 .r31 1, .subi .r30 .r30 1]) (.nonzero .d .r30)

/-- The zero bytes after the key (`r10` of them), XORed likewise. -/
def padLoop : Prog isa :=
  .loop (.block [.add .r11 .r26 .r31, .stb .r12 .r11 32, .add .r11 .r28 .r31, .stb .r0 .r11 32,
    .addi .r31 .r31 1, .subi .r10 .r10 1]) (.nonzero .d .r10)

/-- `init`, but for saving the link register. -/
def initMain : Prog isa :=
  .seq (.block (save .r7 ++ [mov .r26 .r3, mov .r27 .r7, mov .r28 .r4, mov .r29 .r5, mov .r30 .r6] ++
      h0 .r26 ++ h0 .r28 ++ [.li .r12 0x36, .li .r0 0x5c, .li .r31 0]))
  (.seq (.ite (.zero .d .r30) (.block []) keyLoop)
  (.seq (.block [.li .r10 64, .sub .r10 .r10 .r31])
  (.seq (.ite (.zero .d .r10) (.block []) padLoop)
  (.seq (.block [.addi .r4 .r26 32])
  (.seq compressAt
  (.seq (.block [mov .r26 .r28, .addi .r4 .r26 32])
  (.seq compressAt
    (.block restore))))))))

def init : Prog isa :=
  .seq (.block [.mflr .r0]) (.seq (.frame (.push .r0) initMain (.pop .r0)) (.block [.mtlr .r0]))

/-! ## `finalize`

The outer hash value is first copied to `scratch[208..240)`; the inner state
is finalized into `scratch[176..208)`; then the inner state is overwritten
with the outer hash value and that digest, so that it represents
`(K₀ ⊕ opad) ‖ digest`, and finalized again into `out`.

`out`, `inner` and `scratch` are kept in `r23`, `r24` and `r25`, which the
calls of `vg_sha256_finalize` preserve and never even write (so the taint
analysis knows they are still public after them); our caller's values of
those are saved in `scratch[240..248)` and `scratch[160..176)`, and our
return address in a stack frame. -/

/-- Copying 32-bit word `k` from `o₁(src)` to `o₂(dst)`. -/
def cp32 (src dst : Reg) (o₁ o₂ k : Nat) : List Instr :=
  [.load .w .r8 src (o₁ + 4 * k), .store .w .r8 dst (o₂ + 4 * k)]

/-- Copying 64-bit word `k` from `o₁(src)` to `o₂(dst)`. -/
def cp64 (src dst : Reg) (o₁ o₂ k : Nat) : List Instr :=
  [.load .d .r8 src (o₁ + 8 * k), .store .d .r8 dst (o₂ + 8 * k)]

/-- The outer hash value into `scratch[208..240)`. -/
def saveOuter : List Instr := (List.range 8).flatMap (cp32 .r4 .r7 0 208)

/-- The outer hash value and the first digest into the inner state. -/
def loadOuter : List Instr :=
  (List.range 8).flatMap (cp32 .r25 .r24 208 0) ++ (List.range 4).flatMap (cp64 .r25 .r24 176 32)

/-- A call of `vg_sha256_finalize`. -/
def sha256Finalize : Prog isa := .call "vg_sha256_finalize" Impl.Sha256.PPC64LE.Stream.finalize

/-- `finalize`, but for saving the link register. -/
def finalizeMain : Prog isa :=
  .seq (.block ([.store .d .r23 .r7 240, .store .d .r24 .r7 160, .store .d .r25 .r7 168,
      mov .r23 .r6, mov .r24 .r3, mov .r25 .r7] ++ saveOuter ++
      [mov .r4 .r5, .addi .r5 .r7 176, mov .r6 .r7]))
  (.seq sha256Finalize
  (.seq (.block (loadOuter ++ [mov .r3 .r24, .li .r4 96, mov .r5 .r23, mov .r6 .r25]))
  (.seq sha256Finalize
    (.block [.load .d .r23 .r25 240, .load .d .r24 .r25 160, .load .d .r25 .r25 168]))))

def finalize : Prog isa :=
  .seq (.block [.mflr .r0]) (.seq (.frame (.push .r0) finalizeMain (.pop .r0)) (.block [.mtlr .r0]))

end VG.Impl.Hmac.PPC64LE
