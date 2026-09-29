import VerifiedGarbage.Impl.ChaCha20.Arm

/-!
# ChaCha20 keystream XOR: 32-bit ARM implementation

`vg_chacha20_xor(state = r0, data = r1, len = r2, buf = r3)`.

For each 64 bytes of data (the last piece may be shorter),
`vg_chacha20_block(state, buf)` is called, the first `n = min(64, remaining)`
bytes of its output (the first 64 bytes of `buf`) are XORed into the data a
byte at a time, and the block counter (word 12 of the state) is incremented
modulo 2³².

The block function takes `state` in `r0` and `buf` in `r1`. It never writes
`r1`, so `buf` stays there throughout; it overwrites `r0`, so `state` is kept
in `r4` and copied to `r0` before each call. The data not yet processed and
its length are kept in `r5` and `r6`. The block function preserves `r4`–`r6`
(and a call changes only `lr` and `r12` besides what the callee writes). Our
caller's `r4`–`r6`, and our return address (`lr`, which each call replaces),
are saved in `buf[256, 272)`, which is not passed to the block function; so no
stack is used. On return, `r0` is `state` and `r1` is `buf`.

The data is consumed through `r5`, which advances, and the keystream through
`r3 = buf + i`. `remaining < 64` iff `remaining >> 6 = 0`, and the loops count
down to zero, tested with `cmp`/`subs` and `eq`/`ne`. The branches are on the
length only, and every address is a pointer plus a constant or a count, so
only the pointers and the length can affect timing.
-/

namespace VG.Impl.ChaCha20.Arm.Xor

open VG.Arm
open VG.Impl.ChaCha20.Arm (block)

/-- The registers saved in `buf`, and where. -/
def saved : List (Reg × Nat) := [(.r4, 256), (.r5, 260), (.r6, 264), (.lr, 268)]

/-- Save them, with `buf` in `r3`. -/
def save : List Instr := saved.map fun (r, d) => .str r .r3 d
/-- Restore them, with `buf` in `r1`. -/
def restore : List Instr := saved.map fun (r, d) => .ldr r .r1 d

/-- XORs the next `r2` bytes of the keystream (from `r3`) into the data (at
`r5`), advancing both. -/
def xorLoop : Prog isa :=
  .loop (.block [.ldrb .r0 .r5 0, .ldrb .r12 .r3 0, .dp .eor .r0 .r0 (.reg .r12), .strb .r0 .r5 0,
    .dp .add .r5 .r5 (.imm 1), .dp .add .r3 .r3 (.imm 1), .subs .r2 .r2 (.imm 1)]) .ne

/-- One block: the keystream into `buf`, `r2 = min(64, r6)` bytes of it
XORed into the data, and the counter incremented; then whether data remains. -/
def body : Prog isa :=
  .seq (.block [.mov .r0 (.reg .r4)])
  (.seq (.call "vg_chacha20_block" block)
  (.seq (.block [.mov .r2 (.shifted .r6 .lsr 6), .cmp .r2 (.imm 0)])
  (.seq (.ite .eq (.block [.mov .r2 (.reg .r6)]) (.block [.mov .r2 (.imm 64)]))
  (.seq (.block [.dp .sub .r6 .r6 (.reg .r2), .mov .r3 (.reg .r1)])
  (.seq xorLoop
    (.block [.ldr .r0 .r4 48, .dp .add .r0 .r0 (.imm 1), .str .r0 .r4 48, .cmp .r6 (.imm 0)]))))))

def xor : Prog isa :=
  .seq (.block (save ++ [.mov .r4 (.reg .r0), .mov .r5 (.reg .r1), .mov .r6 (.reg .r2),
    .mov .r1 (.reg .r3), .cmp .r6 (.imm 0)]))
  (.seq (.ite .eq (.block []) (.loop body .ne))
    (.block (.mov .r0 (.reg .r4) :: restore)))

end VG.Impl.ChaCha20.Arm.Xor
