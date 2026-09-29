import VerifiedGarbage.Impl.ChaCha20.AArch64

/-!
# ChaCha20 keystream XOR: AArch64 implementation

`vg_chacha20_xor(state = x0, data = x1, len = x2, buf = x3)`.

For each 64 bytes of data (the last piece may be shorter),
`vg_chacha20_block(state, buf)` is called, the first `n = min(64, remaining)`
bytes of its output (the first 64 bytes of `buf`) are XORed into the data a
byte at a time, and the block counter (word 12 of the state) is incremented
modulo 2³².

The block function takes `state` in `x0` and `buf` in `x1`, and writes
neither (it writes only `x2`–`x17`, and a call changes `x16`, `x17` and
`x30`), so they stay there throughout, and on return `x0` is `state` and
`x1` is `buf`. The data not yet processed and its length are kept across the
calls in `x19` and `x20`, which the block function preserves. Our caller's
values of those, and our return address (`x30`, which each call replaces),
are saved in `buf[256, 280)`, which is not passed to the block function; so
no stack is used.

The model has no register-offset addressing: the data is consumed through
`x19`, which advances, and the keystream through `x7 = buf + i`. It has no
flags either: `remaining < 64` iff `remaining >> 6 = 0`, and the loops count
down to zero, tested with `cbz`/`cbnz`. The branches are on the length only,
and every address is a pointer plus a constant or a count, so only the
pointers and the length can affect timing.
-/

namespace VG.Impl.ChaCha20.AArch64.Xor

open VG.AArch64
open VG.Impl.ChaCha20.AArch64 (block)

/-- `mov d, n` (as `add d, n, #0`). -/
def mov (d n : Reg) : Instr := .addImm .x d n 0

/-- The registers saved in `buf`, and where. -/
def saved : List (Reg × Nat) := [(.x19, 256), (.x20, 264), (.x30, 272)]

/-- Save them, with `buf` in `x3`. -/
def save : List Instr := saved.map fun (r, d) => .str .x r .x3 d
/-- Restore them, with `buf` in `x1`. -/
def restore : List Instr := saved.map fun (r, d) => .ldr .x r .x1 d

/-- XORs the next `x2` bytes of the keystream (from `x7`) into the data (at
`x19`), advancing both. -/
def xorLoop : Prog isa :=
  .loop (.block [.ldrb .x6 .x19 0, .ldrb .x8 .x7 0, .logic .eor .w .x6 .x6 .x8, .strb .x6 .x19 0,
    .addImm .x .x19 .x19 1, .addImm .x .x7 .x7 1, .subImm .x .x2 .x2 1]) (.nonzero .x .x2)

/-- One block: the keystream into `buf`, `x2 = min(64, x20)` bytes of it
XORed into the data, and the counter incremented. -/
def body : Prog isa :=
  .seq (.call "vg_chacha20_block" block)
  (.seq (.block [.lsr .x .x9 .x20 6, mov .x2 .x20])
  (.seq (.ite (.zero .x .x9) (.block []) (.block [.movz .x .x2 64 0]))
  (.seq (.block [.sub .x .x20 .x20 .x2, mov .x7 .x1])
  (.seq xorLoop
    (.block [.ldr .w .x3 .x0 48, .addImm .w .x3 .x3 1, .str .w .x3 .x0 48])))))

def xor : Prog isa :=
  .seq (.block (save ++ [mov .x19 .x1, mov .x20 .x2, mov .x1 .x3]))
  (.seq (.ite (.zero .x .x20) (.block []) (.loop body (.nonzero .x .x20)))
    (.block restore))

end VG.Impl.ChaCha20.AArch64.Xor
