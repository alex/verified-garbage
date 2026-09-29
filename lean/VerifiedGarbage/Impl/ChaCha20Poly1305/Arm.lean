import VerifiedGarbage.Impl.ChaCha20.Arm.Xor
import VerifiedGarbage.Impl.Poly1305.Arm

/-!
# ChaCha20-Poly1305: 32-bit ARM implementation

`vg_chacha20_poly1305_seal(ctx = r0, aad = r1, aad_len = r2, data = r3, len = [sp])`
and `vg_chacha20_poly1305_open` (the same arguments, returning `r0`), composed
of calls of the verified ChaCha20 and Poly1305 functions.

The context (1024 bytes, see `VG.Spec.ChaCha20Poly1305.sealContract`):

* `[0, 32)`: the key; `[32, 44)`: the nonce; `[48, 64)`: the tag;
* `[0, 320)`, once the key, the nonce and the tag have been used: the
  working space of `vg_chacha20_block` and `vg_chacha20_xor` (the first 32
  bytes of the block with counter 0 are the one-time Poly1305 key), and then
  the Poly1305 state (`[0, 128)`);
* `[320, 384)`: the ChaCha20 state;
* `[384, 416)`: the one-time key;
* `[416, 432)`: the padded last block of the additional data or the data;
* `[432, 448)`: the lengths block;
* `[448, 464)`: the tag computed;
* `[464, 480)`: the tag received (`open`);
* `[480, 516)`: our caller's `r4`–`r11` and our return address `lr`;
* `[640, 768)`: the working space of `vg_poly1305_finalize` (`scratch`).

`r7` holds the context, `r8` the additional data, `r9` its length, `r10`
the data and `r11` its length throughout: they are callee-saved, so every
callee restores them. `r0`–`r3` and `r12` are temporaries.

`vg_poly1305_finalize(state, count, out, scratch)` takes `out` and
`scratch` on the stack: a frame pushes them (`push {r1, r12}`, `out` at
`[sp]`), around the call, and its pop loads `out` back. So the functions use
8 bytes of stack. `count` is the length of the message authenticated,
`16 (⌈aad_len / 16⌉ + ⌈len / 16⌉ + 1)`, computed in 16-byte blocks (fewer
than 2²⁹) and shifted into `r2:r3`.

The model has no register-offset addressing: a padded last block is copied a
byte at a time through advancing pointers, counting down to zero with `subs`
and `bne`, and the tags are compared without a branch, as
`1 - ((x | -x) >> 31)` of the OR of their XORs `x`.

Constant time: only the pointers and the lengths can affect timing (the
branches are on the lengths, and every address is a pointer plus a constant
or a count). The callees save our registers in memory and restore them, so
for the taint analysis, which follows them through public slots of known
regions, every callee's working space starts at the context (`[0, 320)` for
ChaCha20, the Poly1305 state at `[0, 128)`), and `r7` is set from the
callee's pointer that it keeps (`r1` for ChaCha20, `r0` for Poly1305) after
each call.
-/

namespace VG.Impl.ChaCha20Poly1305.Arm

open VG.Arm

/-! ## Offsets in the context -/

/-- The ChaCha20 state. -/
def stOff : Nat := 320
/-- The one-time key. -/
def keyOff : Nat := 384
/-- The padded last block. -/
def padOff : Nat := 416
/-- The lengths block. -/
def lenOff : Nat := 432
/-- The tag computed. -/
def tagOff : Nat := 448
/-- The tag received, in `open`. -/
def rtagOff : Nat := 464
/-- The saved registers. -/
def savOff : Nat := 480
/-- The working space of `vg_poly1305_finalize`. -/
def scrOff : Nat := 640

/-! ## Saving and restoring the registers -/

/-- The registers saved in the context, and where. -/
def saved : List (Reg × Nat) :=
  [(.r4, 480), (.r5, 484), (.r6, 488), (.r7, 492), (.r8, 496), (.r9, 500), (.r10, 504), (.r11, 508),
   (.lr, 512)]

/-- Save them, with the context in `r0`. -/
def save : List Instr := saved.map fun (r, d) => .str r .r0 d
/-- Restore them, with the context in `r12`. -/
def restore : List Instr := .mov .r12 (.reg .r7) :: saved.map fun (r, d) => .ldr r .r12 d

/-- The arguments moved to where they are kept. -/
def moves : List Instr :=
  [.mov .r7 (.reg .r0), .mov .r8 (.reg .r1), .mov .r9 (.reg .r2), .mov .r10 (.reg .r3), .ldrSp .r11 0]

/-! ## The ChaCha20 state -/

/-- The ChaCha20 constants. -/
def consts : List (BitVec 32) := [0x61707865, 0x3320646e, 0x79622d32, 0x6b206574]

/-- Word `k` of the ChaCha20 state for counter 0 into `r12`: a constant (0–3),
the key (4–11), the counter (12) or the nonce (13–15). -/
def stSrc (k : Nat) : List Instr :=
  if k < 4 then
    let c := consts.getD k 0
    [.movw .r12 (c.extractLsb' 0 16), .movt .r12 (c.extractLsb' 16 16)]
  else if k < 12 then [.ldr .r12 .r7 (4 * (k - 4))]
  else if k = 12 then [.mov .r12 (.imm 0)]
  else [.ldr .r12 .r7 (32 + 4 * (k - 13))]

/-- Word `k` of the ChaCha20 state, at `r7 + stOff + 4k`. -/
def stW (k : Nat) : List Instr := stSrc k ++ [.str .r12 .r7 (stOff + 4 * k)]

/-- The ChaCha20 state for counter 0. -/
def initState : List Instr := (List.range 16).flatMap stW

/-- Copies the `n` words at `r7 + a` to `r7 + b`. -/
def copyWords (a b n : Nat) : List Instr :=
  (List.range n).flatMap fun i => [.ldr .r12 .r7 (a + 4 * i), .str .r12 .r7 (b + 4 * i)]

/-! ## The calls -/

/-- The block with counter 0 into `ctx[0, 64)`, and its first 32 bytes (the
one-time key) copied to `ctx[384, 416)`. -/
def keyGen : Prog isa :=
  .seq (.block [.dp .add .r0 .r7 (.imm (BitVec.ofNat 32 stOff)), .mov .r1 (.reg .r7)])
  (.seq (.call "vg_chacha20_block" Impl.ChaCha20.Arm.block)
    (.block (.mov .r7 (.reg .r1) :: copyWords 0 keyOff 8)))

/-- The Poly1305 state for the one-time key, at `ctx[0, 128)`. -/
def polyInit : Prog isa :=
  .seq (.block [.mov .r0 (.reg .r7), .dp .add .r1 .r7 (.imm (BitVec.ofNat 32 keyOff))])
  (.seq (.call "vg_poly1305_init" Impl.Poly1305.Arm.init)
    (.block [.mov .r7 (.reg .r0)]))

/-- Absorbs `r2` blocks at `r1`. -/
def absorb : Prog isa :=
  .seq (.block [.mov .r0 (.reg .r7)])
  (.seq (.call "vg_poly1305_blocks" Impl.Poly1305.Arm.blocks)
    (.block [.mov .r7 (.reg .r0)]))

/-- Copies the `r3` (nonzero) bytes at `r1` to `r2`, advancing both. -/
def copyLoop : Prog isa :=
  .loop (.block [.ldrb .r12 .r1 0, .strb .r12 .r2 0, .dp .add .r1 .r1 (.imm 1),
    .dp .add .r2 .r2 (.imm 1), .subs .r3 .r3 (.imm 1)]) .ne

/-- The last `r3` bytes (1 to 15), at `r1`, padded with zeros, absorbed. -/
def padTail : Prog isa :=
  .seq (.block [.mov .r12 (.imm 0), .str .r12 .r7 padOff, .str .r12 .r7 (padOff + 4),
    .str .r12 .r7 (padOff + 8), .str .r12 .r7 (padOff + 12),
    .dp .add .r2 .r7 (.imm (BitVec.ofNat 32 padOff))])
  (.seq copyLoop
  (.seq (.block [.dp .add .r1 .r7 (.imm (BitVec.ofNat 32 padOff)), .mov .r2 (.imm 1)]) absorb))

/-- The `n` bytes at `p`, padded with zeros to a multiple of 16, absorbed. -/
def macPad (p n : Reg) : Prog isa :=
  .seq (.block [.mov .r1 (.reg p), .mov .r2 (.shifted n .lsr 4)])
  (.seq absorb
  (.seq (.block [.dp .and .r3 n (.imm 15), .cmp .r3 (.imm 0)])
    (.ite .eq (.block [])
      (.seq (.block [.dp .sub .r1 n (.reg .r3), .dp .add .r1 p (.reg .r1)]) padTail))))

/-- The ChaCha20 counter set to 1, and the data encrypted or decrypted. -/
def crypt : Prog isa :=
  .seq (.block [.mov .r12 (.imm 1), .str .r12 .r7 (stOff + 48),
    .dp .add .r0 .r7 (.imm (BitVec.ofNat 32 stOff)), .mov .r1 (.reg .r10), .mov .r2 (.reg .r11),
    .mov .r3 (.reg .r7)])
  (.seq (.call "vg_chacha20_xor" Impl.ChaCha20.Arm.Xor.xor)
    (.block [.mov .r7 (.reg .r1)]))

/-- The lengths block, absorbed. -/
def lengths : Prog isa :=
  .seq (.block [.str .r9 .r7 lenOff, .mov .r12 (.imm 0), .str .r12 .r7 (lenOff + 4),
    .str .r11 .r7 (lenOff + 8), .str .r12 .r7 (lenOff + 12),
    .dp .add .r1 .r7 (.imm (BitVec.ofNat 32 lenOff)), .mov .r2 (.imm 1)])
    absorb

/-- `⌈n / 16⌉` into `d`, with `t` a temporary: `n / 16 + ((n mod 16) + 15) / 16`. -/
def ceil16 (d t n : Reg) : List Instr :=
  [.mov d (.shifted n .lsr 4), .dp .and t n (.imm 15), .dp .add t t (.imm 15),
   .dp .add d d (.shifted t .lsr 4)]

/-- The arguments of `vg_poly1305_finalize` (but those on the stack): the
state (`r0`), the length of the message in `r2:r3`, and `out` (`r1`, the
tag computed) and `scratch` (`r12`) to push. -/
def finalizeArgs : List Instr :=
  ceil16 .r2 .r3 .r9 ++ ceil16 .r0 .r1 .r11 ++
  [.dp .add .r2 .r2 (.reg .r0), .dp .add .r2 .r2 (.imm 1), .mov .r3 (.shifted .r2 .lsr 28),
   .mov .r2 (.shifted .r2 .lsl 4), .mov .r0 (.reg .r7),
   .dp .add .r1 .r7 (.imm (BitVec.ofNat 32 tagOff)), .dp .add .r12 .r7 (.imm (BitVec.ofNat 32 scrOff))]

/-- The tag computed: `out` and `scratch` pushed as the stack arguments. -/
def finalize : Prog isa :=
  .frame (.push [.r1, .r12]) (.call "vg_poly1305_finalize" Impl.Poly1305.Arm.finalize) (.pop .r1 8)

/-! ## Seal -/

/-- Up to the tag: the registers saved, the one-time key, the data
encrypted, and the MAC of the additional data, the ciphertext and the
lengths, up to the arguments of `vg_poly1305_finalize`. -/
def sealMain : Prog isa :=
  .seq (.block (save ++ moves ++ initState))
  (.seq keyGen
  (.seq crypt
  (.seq polyInit
  (.seq (macPad .r8 .r9)
  (.seq (macPad .r10 .r11)
  (.seq lengths
    (.block finalizeArgs)))))))

/-- The tag copied to `ctx[48, 64)`, and the registers restored. -/
def sealEnd : List Instr := copyWords tagOff 48 4 ++ restore

def «seal» : Prog isa := .seq sealMain (.seq finalize (.block sealEnd))

/-! ## Open -/

/-- Up to the tag: the registers saved, the tag received kept, the one-time
key, and the MAC of the additional data, the ciphertext and the lengths, up
to the arguments of `vg_poly1305_finalize`. -/
def openMain : Prog isa :=
  .seq (.block (save ++ moves ++ copyWords 48 rtagOff 4 ++ initState))
  (.seq keyGen
  (.seq polyInit
  (.seq (macPad .r8 .r9)
  (.seq (macPad .r10 .r11)
  (.seq lengths
    (.block finalizeArgs))))))

/-- `r0 = 1` if the tag computed (at `r7 + 448`) is the one received (at
`r7 + 464`), else 0, without a branch: with `x` the OR of the XORs of their
words, `(x | -x) >> 31` is 0 if `x = 0` and 1 otherwise. -/
def compare : List Instr :=
  [.ldr .r0 .r7 tagOff, .ldr .r1 .r7 rtagOff, .dp .eor .r0 .r0 (.reg .r1)] ++
  (List.range 3).flatMap (fun i =>
    [.ldr .r1 .r7 (tagOff + 4 * (i + 1)), .ldr .r2 .r7 (rtagOff + 4 * (i + 1)),
     .dp .eor .r1 .r1 (.reg .r2), .dp .orr .r0 .r0 (.reg .r1)]) ++
  [.mov .r1 (.imm 0), .dp .sub .r1 .r1 (.reg .r0), .dp .orr .r0 .r0 (.reg .r1),
   .mov .r0 (.shifted .r0 .lsr 31), .mov .r1 (.imm 1), .dp .sub .r0 .r1 (.reg .r0)]

/-- The data decrypted, the tags compared, and the registers restored. -/
def openEnd : Prog isa := .seq crypt (.block (compare ++ restore))

def «open» : Prog isa := .seq openMain (.seq finalize openEnd)

end VG.Impl.ChaCha20Poly1305.Arm
