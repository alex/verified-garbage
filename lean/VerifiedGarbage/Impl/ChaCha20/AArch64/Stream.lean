import VerifiedGarbage.Impl.ChaCha20.AArch64.XorCallee

/-!
# Streaming ChaCha20: AArch64 implementation

`vg_chacha20_init(state = x0, key = x1, nonce = x2)`,
`vg_chacha20_set_nonce(state = x0, nonce = x1)` and
`vg_chacha20_apply(state = x0, data = x1, len = x2) -> w0`, on the streaming
state of `VG.Spec.ChaCha20.restAt` (768 bytes):

* `[0, 64)`: the 16-word state, `[64, 128)`: the buffered block,
  `[128, 136)`: the number of bytes of keystream left;
* `[192, 256)`: the copy of the 16-word state that `vg_chacha20_xor` is
  given (it leaves its state unspecified), `[256, 576)`: its working space;
* `[576, 608)`: our caller's `x21`–`x23` and our return address `x30`
  (which each call replaces); `[608, 616)`: the number of bytes left after
  `apply`, stored there first since the block function overwrites
  `[64, 320)`.

`set_nonce` writes the constants, the nonce (words 12–15) and the number of
bytes left, 64 × (2³² − c) for the initial block counter `c`; `init` also
copies the key, then does the same.

`apply` compares the number of bytes left with `len`, and those left in the
buffered block (the last `left % 64`) with `len`, first: the model has no
flags to branch on, so each comparison's carry (`subs`) is moved into a
register (`adcs` of zeros) and tested with `cbz`. If fewer than `len` bytes
are left it returns 0 at once. Otherwise it XORs the bytes left in the
buffered block (as many as `len` asks for), then the whole blocks that
follow with `vg_chacha20_xor` (an implementation `x` of it: `apply` is
generic over them), advancing the counter, and finally, if bytes remain,
computes the next block into the buffer with `vg_chacha20_block`, advances
the counter and XORs its first bytes. `x21` holds the state, `x22` the data
not yet processed and `x23` its length throughout: they are callee-saved,
so the callees keep them. A call (`bl`) stores nothing in memory, so no
stack is used.

The branches are on the length and the number of bytes left only, and every
address is a pointer plus a constant, or advances by one: only the pointers,
the length and the number of bytes left (which the contract lets `apply`
leak) can affect timing.
-/

namespace VG.Impl.ChaCha20.AArch64.Stream

open VG.AArch64
open VG.Impl.ChaCha20.AArch64 (XorCallee block)
open VG.Impl.ChaCha20.AArch64.Xor (mov)

/-- The nonce at `x1`, the constants and the number of bytes left, into the
state at `x0`. -/
def setNonceInstrs : List Instr :=
  [.ldr .x .x9 .x1 0, .ldr .x .x10 .x1 8, .ldr .w .x11 .x1 0, .str .x .x9 .x0 48, .str .x .x10 .x0 56,
   .movz .x .x12 0x7865 0, .movk .x .x12 0x6170 1, .movk .x .x12 0x646e 2, .movk .x .x12 0x3320 3,
   .str .x .x12 .x0 0,
   .movz .x .x12 0x2d32 0, .movk .x .x12 0x7962 1, .movk .x .x12 0x6574 2, .movk .x .x12 0x6b20 3,
   .str .x .x12 .x0 8,
   .movz .x .x13 1 2, .sub .x .x13 .x13 .x11, .lsl .x .x13 .x13 6, .str .x .x13 .x0 128]

def setNonce : Prog isa := .block setNonceInstrs

/-- The key at `x1` into words 4–11, and the nonce pointer into `x1`. -/
def keyInstrs : List Instr :=
  [.ldr .x .x9 .x1 0, .ldr .x .x10 .x1 8, .ldr .x .x11 .x1 16, .ldr .x .x12 .x1 24,
   .str .x .x9 .x0 16, .str .x .x10 .x0 24, .str .x .x11 .x0 32, .str .x .x12 .x0 40, mov .x1 .x2]

def init : Prog isa := .block (keyInstrs ++ setNonceInstrs)

/-! ## `apply` -/

/-- `x9` = the bytes left, `x10` = those in the buffered block,
`x11` = 1 iff at least `len` are left, `x12` = 1 iff the buffered block has
at least `len`. -/
def check : List Instr :=
  [.ldr .x .x9 .x0 128, .subs .x .x13 .x9 .x2, .movz .x .x11 0 0, .adcs .x .x11 .x11 .x11,
   .lsl .x .x10 .x9 58, .lsr .x .x10 .x10 58,
   .subs .x .x13 .x10 .x2, .movz .x .x12 0 0, .adcs .x .x12 .x12 .x12]

/-- Saves our caller's registers and our return address, moves the arguments
where they are kept, and stores the bytes left after `apply`. -/
def start : List Instr :=
  [.str .x .x21 .x0 576, .str .x .x22 .x0 584, .str .x .x23 .x0 592, .str .x .x30 .x0 600,
   mov .x21 .x0, mov .x22 .x1, mov .x23 .x2, .sub .x .x9 .x9 .x2, .str .x .x9 .x21 608]

/-- XORs the `x2` bytes at `x1` into the data (`x22`), advancing both, and
counting them off `x23`. -/
def xorBytes : Prog isa :=
  .ite (.zero .x .x2) (.block [])
    (.loop (.block [.ldrb .x9 .x22 0, .ldrb .x10 .x1 0, .logic .eor .w .x9 .x9 .x10, .strb .x9 .x22 0,
      .addImm .x .x22 .x22 1, .addImm .x .x1 .x1 1, .subImm .x .x2 .x2 1, .subImm .x .x23 .x23 1])
      (.nonzero .x .x2))

/-- Everything up to the call of `vg_chacha20_xor`: the bytes left in the
buffered block, `x2 = min(x10, len)` of them, from `x21 + 128 - x10`; then
`x2` = the bytes of the whole blocks that follow (`x23` rounded down to a
multiple of 64). -/
def part1 : Prog isa :=
  .seq (.block start)
  (.seq (.ite (.zero .x .x12) (.block [mov .x2 .x10]) (.block []))
  (.seq (.block [.addImm .x .x1 .x21 128, .sub .x .x1 .x1 .x10])
  (.seq xorBytes
    (.block [.lsr .x .x2 .x23 6, .lsl .x .x2 .x2 6]))))

/-- The whole blocks: the state copied and the counter advanced (the low
half of `x15` is word 12), then `vg_chacha20_xor` (`x`) on the copy. -/
def blocksArgs : List Instr :=
  [.ldr .x .x9 .x21 0, .ldr .x .x10 .x21 8, .ldr .x .x11 .x21 16, .ldr .x .x12 .x21 24,
   .ldr .x .x13 .x21 32, .ldr .x .x14 .x21 40, .ldr .x .x15 .x21 48, .ldr .x .x16 .x21 56,
   .str .x .x9 .x21 192, .str .x .x10 .x21 200, .str .x .x11 .x21 208, .str .x .x12 .x21 216,
   .str .x .x13 .x21 224, .str .x .x14 .x21 232, .str .x .x15 .x21 240, .str .x .x16 .x21 248,
   .lsr .x .x17 .x2 6, .add .w .x15 .x15 .x17, .str .w .x15 .x21 48,
   .addImm .x .x0 .x21 192, mov .x1 .x22, .addImm .x .x3 .x21 256,
   .add .x .x22 .x22 .x2, .sub .x .x23 .x23 .x2]

def part2 (x : XorCallee) : Prog isa :=
  .ite (.zero .x .x2) (.block []) (.seq (.block blocksArgs) (.call x.name x.code))

/-- The arguments of the block function: the state and the buffer. -/
def tailArgs : List Instr := [mov .x0 .x21, .addImm .x .x1 .x21 64]

/-- After the block function: the counter advanced, and `x23` bytes of the
block XORed. -/
def tailXor : Prog isa :=
  .seq (.block [.ldr .w .x9 .x21 48, .addImm .w .x9 .x9 1, .str .w .x9 .x21 48, .addImm .x .x1 .x21 64,
    mov .x2 .x23])
    xorBytes

/-- The last bytes, if any: the next block into the buffer, the counter
advanced, and `x23` bytes of the block XORed. -/
def part3 : Prog isa :=
  .ite (.zero .x .x23) (.block [])
    (.seq (.block tailArgs) (.seq (.call "vg_chacha20_block" block) tailXor))

/-- The bytes left stored, our caller's registers and our return address
restored, and 1 returned. -/
def finish : List Instr :=
  [.ldr .x .x9 .x21 608, .str .x .x9 .x21 128, .ldr .x .x30 .x21 600, .ldr .x .x22 .x21 584,
   .ldr .x .x23 .x21 592, .ldr .x .x21 .x21 576, .movz .x .x0 1 0]

def apply (x : XorCallee) : Prog isa :=
  .seq (.block check)
  (.ite (.zero .x .x11) (.block [.movz .x .x0 0 0])
    (.seq part1 (.seq (part2 x) (.seq part3 (.block finish)))))

end VG.Impl.ChaCha20.AArch64.Stream
