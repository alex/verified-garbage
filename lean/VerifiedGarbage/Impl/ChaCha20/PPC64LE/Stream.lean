import VerifiedGarbage.Impl.ChaCha20.PPC64LE.Xor

/-!
# Streaming ChaCha20: PPC64LE implementation

`vg_chacha20_init(state = r3, key = r4, nonce = r5)`,
`vg_chacha20_set_nonce(state = r3, nonce = r4)` and
`vg_chacha20_apply(state = r3, data = r4, len = r5) -> r3`, on the streaming
state of `VG.Spec.ChaCha20.restAt` (768 bytes), laid out as on AArch64
(`VG.Impl.ChaCha20.AArch64.Stream`):

* `[0, 64)`: the 16-word state, `[64, 128)`: the buffered block,
  `[128, 136)`: the number of bytes of keystream left;
* `[192, 256)`: the copy of the 16-word state that `vg_chacha20_xor` is
  given (it leaves its state unspecified), `[256, 576)`: its working space;
* `[576, 608)`: our caller's `r24`–`r26` and our return address (which each
  call replaces); `[608, 616)`: the number of bytes left after `apply`,
  stored there first since the block function overwrites `[64, 320)`.

`set_nonce` writes the constants, the nonce (words 12–15) and the number of
bytes left, 64 × (2³² − c) for the initial block counter `c`; `init` also
copies the key, then does the same.

`apply` compares the number of bytes left with `len`, and those left in the
buffered block (the last `left % 64`) with `len`, first: the model has no
compare instructions, so each comparison is computed as a number, 1 iff
`a < b` (`borrow`), and tested for zero. If fewer than `len` bytes are left it
returns 0 at once. Otherwise it XORs the bytes left in the buffered block (as
many as `len` asks for), then the whole blocks that follow with
`vg_chacha20_xor`, advancing the counter, and finally, if bytes remain,
computes the next block into the buffer with `vg_chacha20_block`, advances
the counter and XORs its first bytes. `r24` holds the state, `r25` the data
not yet processed and `r26` its length throughout: neither callee writes
them. A call (`bl`) stores nothing in memory, so no stack is used.

The branches are on the length and the number of bytes left only, and every
address is a pointer plus a constant, or advances by one: only the pointers,
the length and the number of bytes left (which the contract lets `apply`
leak) can affect timing.
-/

namespace VG.Impl.ChaCha20.PPC64LE.Stream

open VG.PPC64LE
open VG.Impl.ChaCha20.PPC64LE (block)
open VG.Impl.ChaCha20.PPC64LE.Xor (mov xor)

/-- The 32-bit word `v` into `off(r3)`, built in `r10`. -/
def word (v : BitVec 32) (off : Nat) : List Instr :=
  [.lis .r10 (v.extractLsb' 16 16), .ori .r10 .r10 (v.extractLsb' 0 16), .store .w .r10 .r3 off]

/-- The nonce at `r4`, the constants and the number of bytes left, into the
state at `r3`. -/
def setNonceInstrs : List Instr :=
  [.load .w .r9 .r4 0, .load .w .r10 .r4 4, .load .w .r11 .r4 8, .load .w .r12 .r4 12,
   .store .w .r9 .r3 48, .store .w .r10 .r3 52, .store .w .r11 .r3 56, .store .w .r12 .r3 60] ++
  word 0x61707865 0 ++ word 0x3320646e 4 ++ word 0x79622d32 8 ++ word 0x6b206574 12 ++
  [.li .r12 1, .lsl .r12 .r12 32, .sub .r12 .r12 .r9, .lsl .r12 .r12 6, .store .d .r12 .r3 128]

def setNonce : Prog isa := .block setNonceInstrs

/-- The key at `r4` into words 4–11, and the nonce pointer into `r4`. -/
def keyInstrs : List Instr :=
  [.load .d .r9 .r4 0, .load .d .r10 .r4 8, .load .d .r11 .r4 16, .load .d .r12 .r4 24,
   .store .d .r9 .r3 16, .store .d .r10 .r3 24, .store .d .r11 .r3 32, .store .d .r12 .r3 40, mov .r4 .r5]

def init : Prog isa := .block (keyInstrs ++ setNonceInstrs)

/-! ## `apply` -/

/-- `d` = 1 iff `a < b` (unsigned), from `r12` = 1; writes `r6`, `r11` and
`d`. With `a = 2aₕ + aₗ` and `b = 2bₕ + bₗ`, `aₕ − bₕ − (aₗ < bₗ)` fits in a
signed 64-bit word and is negative iff `a < b`; `aₗ < bₗ` is the sign of
`aₗ − bₗ`. -/
def borrow (d a b : Reg) : List Instr :=
  [.lsr .d d a 1, .lsr .d .r11 b 1, .sub d d .r11, .logic .and .r11 a .r12, .logic .and .r6 b .r12,
   .sub .r11 .r11 .r6, .lsr .d .r11 .r11 63, .sub d d .r11, .lsr .d d d 63]

/-- `r9` = the bytes left, `r7` = those in the buffered block,
`r10` = 1 iff fewer than `len` are left, `r8` = 1 iff the buffered block has
fewer than `len`. -/
def check : List Instr :=
  [.load .d .r9 .r3 128, .li .r12 1, .li .r7 63, .logic .and .r7 .r9 .r7] ++
  borrow .r10 .r9 .r5 ++ borrow .r8 .r7 .r5

/-- Saves our caller's registers and our return address, moves the arguments
where they are kept, and stores the bytes left after `apply`. -/
def start : List Instr :=
  [.store .d .r24 .r3 576, .store .d .r25 .r3 584, .store .d .r26 .r3 592, .mflr .r0, .store .d .r0 .r3 600,
   mov .r24 .r3, mov .r25 .r4, mov .r26 .r5, .sub .r9 .r9 .r5, .store .d .r9 .r24 608]

/-- XORs the `r5` bytes at `r4` into the data (`r25`), advancing both, and
counting them off `r26`. -/
def xorBytes : Prog isa :=
  .ite (.zero .d .r5) (.block [])
    (.loop (.block [.lbz .r9 .r25 0, .lbz .r10 .r4 0, .logic .xor .r9 .r9 .r10, .stb .r9 .r25 0,
      .addi .r25 .r25 1, .addi .r4 .r4 1, .subi .r5 .r5 1, .subi .r26 .r26 1])
      (.nonzero .d .r5))

/-- Everything up to the call of `vg_chacha20_xor`: the bytes left in the
buffered block, `r5 = min(r7, len)` of them, from `r24 + 128 - r7`; then
`r5` = the bytes of the whole blocks that follow (`r26` rounded down to a
multiple of 64). -/
def part1 : Prog isa :=
  .seq (.block start)
  (.seq (.ite (.nonzero .d .r8) (.block [mov .r5 .r7]) (.block []))
  (.seq (.block [.addi .r4 .r24 128, .sub .r4 .r4 .r7])
  (.seq xorBytes
    (.block [.lsr .d .r5 .r26 6, .lsl .r5 .r5 6]))))

/-- The whole blocks: the state copied and the counter advanced (word 12),
then `vg_chacha20_xor` on the copy. -/
def blocksArgs : List Instr :=
  [.load .d .r9 .r24 0, .load .d .r10 .r24 8, .load .d .r11 .r24 16, .load .d .r12 .r24 24,
   .store .d .r9 .r24 192, .store .d .r10 .r24 200, .store .d .r11 .r24 208, .store .d .r12 .r24 216,
   .load .d .r9 .r24 32, .load .d .r10 .r24 40, .load .d .r11 .r24 48, .load .d .r12 .r24 56,
   .store .d .r9 .r24 224, .store .d .r10 .r24 232, .store .d .r11 .r24 240, .store .d .r12 .r24 248,
   .lsr .d .r9 .r5 6, .load .w .r10 .r24 48, .add .r10 .r10 .r9, .store .w .r10 .r24 48,
   .addi .r3 .r24 192, mov .r4 .r25, .addi .r6 .r24 256,
   .add .r25 .r25 .r5, .sub .r26 .r26 .r5]

def part2 : Prog isa :=
  .ite (.zero .d .r5) (.block []) (.seq (.block blocksArgs) (.call "vg_chacha20_xor" xor))

/-- The arguments of the block function: the state and the buffer. -/
def tailArgs : List Instr := [mov .r3 .r24, .addi .r4 .r24 64]

/-- After the block function: the counter advanced, and `r26` bytes of the
block XORed. -/
def tailXor : Prog isa :=
  .seq (.block [.load .w .r9 .r24 48, .addi .r9 .r9 1, .store .w .r9 .r24 48, .addi .r4 .r24 64,
    mov .r5 .r26])
    xorBytes

/-- The last bytes, if any: the next block into the buffer, the counter
advanced, and `r26` bytes of the block XORed. -/
def part3 : Prog isa :=
  .ite (.zero .d .r26) (.block [])
    (.seq (.block tailArgs) (.seq (.call "vg_chacha20_block" block) tailXor))

/-- The bytes left stored, our caller's registers and our return address
restored, and 1 returned. -/
def finish : List Instr :=
  [.load .d .r9 .r24 608, .store .d .r9 .r24 128, .load .d .r0 .r24 600, .mtlr .r0, .load .d .r25 .r24 584,
   .load .d .r26 .r24 592, .load .d .r24 .r24 576, .li .r3 1]

def apply : Prog isa :=
  .seq (.block check)
  (.ite (.nonzero .d .r10) (.block [.li .r3 0])
    (.seq part1 (.seq part2 (.seq part3 (.block finish)))))

end VG.Impl.ChaCha20.PPC64LE.Stream
