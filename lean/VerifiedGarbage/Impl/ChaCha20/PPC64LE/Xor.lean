import VerifiedGarbage.Impl.ChaCha20.PPC64LE

/-!
# ChaCha20 keystream XOR: PPC64LE implementation

`vg_chacha20_xor(state = r3, data = r4, len = r5, buf = r6)`.

For each 64 bytes of data (the last piece may be shorter),
`vg_chacha20_block(state, buf)` is called, the first `n = min(64, remaining)`
bytes of its output (the first 64 bytes of `buf`) are XORed into the data a
byte at a time, and the block counter (word 12 of the state) is incremented
modulo 2³².

The block function takes `state` in `r3` and `buf` in `r4`, and writes
neither (it writes only `r0`, `r5`–`r12` and `r14`–`r21`, and a call changes
`r0`, `r11`, `r12` and the link register), so they stay there throughout.
The data not yet processed and its length are kept across the calls in
`r22` and `r23`, which the block function preserves. Our caller's values of
those, and our return address (the link register, which each call replaces,
moved to `r0`), are saved in `buf[256, 280)`, which is not passed to the
block function; so no stack is used.

Only register-plus-displacement addressing is used: the data is consumed
through `r22`, which advances, and the keystream through `r7 = buf + i`.
`remaining < 64` iff `remaining >> 6 = 0`, and the loops count down to
zero. The branches are on the length only, and every address is a pointer
plus a constant or a count, so only the pointers and the length can affect
timing.
-/

namespace VG.Impl.ChaCha20.PPC64LE.Xor

open VG.PPC64LE
open VG.Impl.ChaCha20.PPC64LE (block)

/-- `mr d, n` (as `addi d, n, 0`; `n` is not `r0`). -/
def mov (d n : Reg) : Instr := .addi d n 0

/-- Save our caller's `r22` and `r23` and our return address, with `buf` in
`r6`. -/
def save : List Instr :=
  [.store .d .r22 .r6 256, .store .d .r23 .r6 264, .mflr .r0, .store .d .r0 .r6 272]

/-- Restore them, with `buf` in `r4`. -/
def restore : List Instr :=
  [.load .d .r0 .r4 272, .mtlr .r0, .load .d .r22 .r4 256, .load .d .r23 .r4 264]

/-- XORs the next `r5` bytes of the keystream (from `r7`) into the data (at
`r22`), advancing both. -/
def xorLoop : Prog isa :=
  .loop (.block [.lbz .r6 .r22 0, .lbz .r8 .r7 0, .logic .xor .r6 .r6 .r8, .stb .r6 .r22 0,
    .addi .r22 .r22 1, .addi .r7 .r7 1, .subi .r5 .r5 1]) (.nonzero .d .r5)

/-- One block: the keystream into `buf`, `r5 = min(64, r23)` bytes of it
XORed into the data, and the counter incremented. -/
def body : Prog isa :=
  .seq (.call "vg_chacha20_block" block)
  (.seq (.block [.lsr .d .r9 .r23 6, mov .r5 .r23])
  (.seq (.ite (.zero .d .r9) (.block []) (.block [.li .r5 64]))
  (.seq (.block [.sub .r23 .r23 .r5, mov .r7 .r4])
  (.seq xorLoop
    (.block [.load .w .r8 .r3 48, .addi .r8 .r8 1, .store .w .r8 .r3 48])))))

def xor : Prog isa :=
  .seq (.block (save ++ [mov .r22 .r4, mov .r23 .r5, mov .r4 .r6]))
  (.seq (.ite (.zero .d .r23) (.block []) (.loop body (.nonzero .d .r23)))
    (.block restore))

end VG.Impl.ChaCha20.PPC64LE.Xor
