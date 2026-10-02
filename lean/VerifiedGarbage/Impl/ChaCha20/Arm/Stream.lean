import VerifiedGarbage.Impl.ChaCha20.Arm.Xor

/-!
# Streaming ChaCha20: 32-bit ARM implementation

`vg_chacha20_init(state = r0, key = r1, nonce = r2)`,
`vg_chacha20_set_nonce(state = r0, nonce = r1)` and
`vg_chacha20_apply(state = r0, data = r1, len = r2) -> r0`, on the streaming
state of `VG.Spec.ChaCha20.restAt` (768 bytes):

* `[0, 64)`: the 16-word state, `[64, 128)`: the buffered block,
  `[128, 136)`: the number of bytes of keystream left (64 bits, low word
  first);
* `[192, 256)`: the copy of the 16-word state that `vg_chacha20_xor` is
  given (it leaves its state unspecified), `[256, 576)`: its working space;
* `[576, 596)`: our caller's `r4`–`r7` and our return address `lr` (which
  each call replaces); `[600, 608)`: the number of bytes left after
  `apply`, stored there first since the block function overwrites
  `[64, 320)`.

`set_nonce` loads the nonce first, then stores it (words 12–15), the number
of bytes left, 64 × (2³² − c) for the initial block counter `c` (computed in
`r3:r12` with `subs` and `adc`, then shifted), and the constants; `init`
copies the key a word at a time first.

The model's branches test only Z, so `apply` moves the carry of each
comparison into a register (`adc` of zeros) and tests that. It first
compares the number of bytes left with `len`; if fewer are left it returns 0
at once. Otherwise it XORs the bytes left in the buffered block (the last
`left % 64`, as many as `len` asks for), then the whole blocks that follow
with `vg_chacha20_xor`, advancing the counter, and finally, if bytes remain,
computes the next block into the buffer with `vg_chacha20_block`, advances
the counter and XORs its first bytes. `r4` holds the state, `r5` the data
not yet processed and `r6` its length throughout, and `r7` the length of the
whole blocks across the call of `vg_chacha20_xor`: they are callee-saved, so
the callees keep them. A call (`bl`) stores nothing in memory, so no stack is
used.

The branches are on the length and the number of bytes left only, and every
address is a pointer plus a constant, or advances by one: only the pointers,
the length and the number of bytes left (which the contract lets `apply`
leak) can affect timing.
-/

namespace VG.Impl.ChaCha20.Arm.Stream

open VG.Arm
open VG.Impl.ChaCha20.Arm (block)
open VG.Impl.ChaCha20.Arm.Xor (xorLoop)

/-- Copies `n` words from `s + so` to `d + dof`, a word at a time through `t`. -/
def copyWords (t s d : Reg) (so dof n : Nat) : List Instr :=
  (List.range n).flatMap fun k => [.ldr t s (so + 4 * k), .str t d (dof + 4 * k)]

/-- The nonce at `r1`, the number of bytes left and the constants, into the
state at `r0`. -/
def setNonceInstrs : List Instr :=
  [.ldr .r2 .r1 0, .ldr .r3 .r1 4, .ldr .r12 .r1 8, .ldr .r1 .r1 12,
   .str .r2 .r0 48, .str .r3 .r0 52, .str .r12 .r0 56, .str .r1 .r0 60,
   .mov .r3 (.imm 0), .subs .r12 .r3 (.reg .r2), .adc .r3 .r3 (.imm 0),
   .mov .r2 (.shifted .r12 .lsr 26), .dp .orr .r3 .r2 (.shifted .r3 .lsl 6), .mov .r12 (.shifted .r12 .lsl 6),
   .str .r12 .r0 128, .str .r3 .r0 132,
   .movw .r1 0x7865, .movt .r1 0x6170, .str .r1 .r0 0,
   .movw .r1 0x646e, .movt .r1 0x3320, .str .r1 .r0 4,
   .movw .r1 0x2d32, .movt .r1 0x7962, .str .r1 .r0 8,
   .movw .r1 0x6574, .movt .r1 0x6b20, .str .r1 .r0 12]

def setNonce : Prog isa := .block setNonceInstrs

/-- The key at `r1` into words 4–11, and the nonce pointer into `r1`. -/
def keyInstrs : List Instr := copyWords .r3 .r1 .r0 0 16 8 ++ [.mov .r1 (.reg .r2)]

def init : Prog isa := .block (keyInstrs ++ setNonceInstrs)

/-! ## `apply` -/

/-- Z = whether fewer than `len` bytes are left: `r3` = (low word ≥ len) +
(high word ≠ 0), each a carry. -/
def check : List Instr :=
  [.ldr .r3 .r0 128, .ldr .r12 .r0 132, .cmp .r3 (.reg .r2), .mov .r3 (.imm 0), .adc .r3 .r3 (.imm 0),
   .subs .r12 .r12 (.imm 1), .adc .r3 .r3 (.imm 0), .cmp .r3 (.imm 0)]

/-- Saves our caller's registers, our return address and the bytes left after
`apply`, moves the arguments where they are kept, and sets Z if the bytes
left in the buffered block (`r12`) are fewer than `len` (`r2`). -/
def start : List Instr :=
  [.str .r4 .r0 576, .str .r5 .r0 580, .str .r6 .r0 584, .str .r7 .r0 588, .str .lr .r0 592,
   .ldr .r3 .r0 128, .ldr .r12 .r0 132, .subs .r3 .r3 (.reg .r2), .movw .r4 0xffff, .movt .r4 0xffff,
   .adc .r12 .r12 (.reg .r4), .str .r3 .r0 600, .str .r12 .r0 604,
   .mov .r4 (.reg .r0), .mov .r5 (.reg .r1), .mov .r6 (.reg .r2),
   .ldr .r12 .r4 128, .dp .and .r12 .r12 (.imm 63), .cmp .r12 (.reg .r6), .mov .r0 (.imm 0),
   .adc .r0 .r0 (.imm 0), .cmp .r0 (.imm 0), .mov .r2 (.reg .r6)]

/-- XORs the `r2` bytes at `r3` into the data (`r5`), advancing both. -/
def xorBytes : Prog isa := .seq (.block [.cmp .r2 (.imm 0)]) (.ite .eq (.block []) xorLoop)

/-- Everything up to the whole blocks: the bytes left in the buffered block,
`r2 = min(r12, len)` of them, from `r4 + 128 - r12`, counted off `r6`; then
`r2` = the bytes of the whole blocks that follow (`r6` rounded down to a
multiple of 64), and Z whether there are none. -/
def part1 : Prog isa :=
  .seq (.block start)
  (.seq (.ite .eq (.block [.mov .r2 (.reg .r12)]) (.block []))
  (.seq (.block [.dp .add .r3 .r4 (.imm 128), .dp .sub .r3 .r3 (.reg .r12), .dp .sub .r6 .r6 (.reg .r2)])
  (.seq xorBytes
    (.block [.mov .r2 (.shifted .r6 .lsr 6), .mov .r2 (.shifted .r2 .lsl 6), .cmp .r2 (.imm 0)]))))

/-- The whole blocks: the state copied and the counter advanced (by `r2 >> 6`),
and the arguments of `vg_chacha20_xor`; their length is kept in `r7`. -/
def blocksArgs : List Instr :=
  copyWords .r0 .r4 .r4 0 192 16 ++
  [.ldr .r0 .r4 48, .mov .r1 (.shifted .r2 .lsr 6), .dp .add .r0 .r0 (.reg .r1), .str .r0 .r4 48,
   .mov .r7 (.reg .r2), .dp .add .r0 .r4 (.imm 192), .mov .r1 (.reg .r5), .dp .add .r3 .r4 (.imm 256)]

def part2 : Prog isa :=
  .ite .eq (.block [])
    (.seq (.block blocksArgs) (.seq (.call "vg_chacha20_xor" Xor.xor)
      (.block [.dp .add .r5 .r5 (.reg .r7), .dp .sub .r6 .r6 (.reg .r7)])))

/-- After the block function: the counter advanced, and `r6` bytes of the
block XORed. -/
def tailXor : Prog isa :=
  .seq (.block [.ldr .r0 .r4 48, .dp .add .r0 .r0 (.imm 1), .str .r0 .r4 48, .dp .add .r3 .r4 (.imm 64),
    .mov .r2 (.reg .r6)])
    xorBytes

/-- The last bytes, if any: the next block into the buffer, the counter
advanced, and `r6` bytes of the block XORed. -/
def part3 : Prog isa :=
  .seq (.block [.cmp .r6 (.imm 0)])
  (.ite .eq (.block [])
    (.seq (.block [.mov .r0 (.reg .r4), .dp .add .r1 .r4 (.imm 64)])
      (.seq (.call "vg_chacha20_block" block) tailXor)))

/-- The bytes left stored, our caller's registers and our return address
restored, and 1 returned. -/
def finish : List Instr :=
  [.ldr .r0 .r4 600, .str .r0 .r4 128, .ldr .r0 .r4 604, .str .r0 .r4 132, .ldr .lr .r4 592,
   .ldr .r5 .r4 580, .ldr .r6 .r4 584, .ldr .r7 .r4 588, .ldr .r4 .r4 576, .mov .r0 (.imm 1)]

def apply : Prog isa :=
  .seq (.block check)
  (.ite .eq (.block [.mov .r0 (.imm 0)])
    (.seq part1 (.seq part2 (.seq part3 (.block finish)))))

end VG.Impl.ChaCha20.Arm.Stream
