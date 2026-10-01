import VerifiedGarbage.Spec.Blake2
import VerifiedGarbage.TCB.Arm.Isa

/-!
# Streaming BLAKE2: 32-bit ARM implementation

`init`, `update` and `finalize` for words of `w` bits (`Spec.Blake2.b` or
`Spec.Blake2.s`), on the streaming state of `Spec.Blake2.Repr`, as on AArch64
(`Impl/Blake2/AArch64/Stream.lean`): the hash value (`N = 8 · w/8` bytes)
followed by a `B`-byte buffer (`B = 16 · w/8`) holding the last block of the
data so far, 1 to `B` bytes of it (none for empty data). The caller keeps the
byte count, `count`, from which the number of buffered bytes follows.

* `init(state = r0, outlen = r1, key = r2, keylen = r3)` stores the initial
  hash value (as 32-bit words) and, for a key, the key block in the buffer.
* `update(state = r0, count = r2:r3, data = [sp], len = [sp, #4],
  scratch = [sp, #8])` fills a non-empty buffer from `data`; compresses it if
  more data follows; compresses every block of the rest of `data` but the
  last straight from `data`; and copies that last one (1 to `B` bytes) to
  the buffer.
* `finalize(state = r0, count = r2:r3, out = [sp], scratch = [sp, #4])` pads
  the buffered block with zeros, compresses it as the last block, and copies
  the hash value to `out`.

The code is the same for any compression function (`name`, `code`) with the
contract `Proof.Blake2.compressArm P`: `compress(state = r0, blocks = r1,
n = r2, t, last, scratch)`, whose `t` (64 bits), `last` and `scratch` are
stack arguments. Each call is in a frame that pushes them (`push {r3, r11,
r12, lr}`: `t` in `r3:r11`, `last` in `r12` and `scratch` in `lr`), which
the pop removes, loading `r3`; so the functions use 16 bytes of stack. The
callee gets `scratch[0, 512)`, and preserves `r4`–`r11`, so our variables
live there: `r4` = `state`, `r5` = `scratch`, `r6` = `data` (advancing),
`r7` = the bytes of `data` left, `r8` = the bytes in the buffer, `r9:r10` =
the byte count; `r11` is a temporary. Our caller's `r4`–`r11` and our return
address (`lr`, which every call replaces) are saved in `scratch[512, 548)`.

`update` calls the compression function twice, unconditionally: first on the
buffer (with `n` = 1 if it is full and more data follows, 0 otherwise), then
on the whole blocks of `data` but the last (`n` may be 0). Only the code
between the calls has branches, and a call is never inside one.

The model has no register-offset addressing, so byte `r` of the buffer is
addressed as `[r1, #N]` with `r1 = state + r` computed just before the
access, and `data` is consumed through a pointer that advances. Every
comparison is a shift or a subtraction tested with `cmp`/`subs` and
`eq`/`ne`. Every address and branch depends only on `sp`, the pointers,
`count`, `len`, `outlen` and `keylen`.
-/

namespace VG.Impl.Blake2.Arm.Stream

open VG.Arm

section
variable (w : Nat)

/-- The size of a word in bytes. -/
def ws : Nat := w / 8
/-- The size of the hash value, where the buffer starts. -/
def N : Nat := 8 * ws w
/-- The block size. -/
def B : Nat := 16 * ws w
/-- The log₂ of the block size. -/
def lbb : Nat := if w = 64 then 7 else 6

end

/-- The callee-saved registers we use (and `lr`), and where they are saved in `scratch`. -/
def saved : List (Reg × Nat) :=
  [(.r4, 512), (.r5, 516), (.r6, 520), (.r7, 524), (.r8, 528), (.r9, 532), (.r10, 536), (.r11, 540),
    (.lr, 544)]

/-- Save them, with `scratch` in `b`. -/
def save (b : Reg) : List Instr := saved.map fun (r, d) => .str r b d

/-- Restore them, from `scratch` in `r5` (copied to `r3` first). -/
def restore : List Instr := .mov .r3 (.reg .r5) :: saved.map fun (r, d) => .ldr r .r3 d

/-- A call of the compression function, in the frame of its stack arguments:
`t` in `r3:r11`, `last` in `r12` and `scratch` in `lr`. -/
def call (name : String) (code : Prog isa) : Prog isa :=
  .frame (.push [.r3, .r11, .r12, .lr]) (.call name code) (.pop .r3 16)

section
variable {w : Nat}

/-- `r8` := the number of bytes in the buffer for the byte count in `r9:r10`:
`((count - 1) mod B) + 1`, or 0 if `count = 0`. -/
def bufLen : Prog isa :=
  .seq (.block [.dp .sub .r8 .r9 (.imm 1), .dp .and .r8 .r8 (.imm (BitVec.ofNat 32 (B w - 1))),
      .dp .add .r8 .r8 (.imm 1), .dp .orr .r12 .r9 (.reg .r10), .cmp .r12 (.imm 0)])
    (.ite .eq (.block [.mov .r8 (.imm 0)]) (.block []))

/-- The loop copying `r11 ≥ 1` bytes of `data` (at `r6`) to the buffer, from
byte `r8` on. -/
def copyLoop : Prog isa :=
  .loop (.block [.ldrb .r12 .r6 0, .dp .add .r1 .r4 (.reg .r8), .strb .r12 .r1 (N w),
    .dp .add .r6 .r6 (.imm 1), .dp .add .r8 .r8 (.imm 1), .subs .r11 .r11 (.imm 1)]) .ne

/-- Copy `r11` bytes of `data` to the buffer (none if `r11 = 0`), and count
them. -/
def copy : Prog isa :=
  .seq (.block [.dp .sub .r7 .r7 (.reg .r11), .adds .r9 .r9 (.reg .r11), .adc .r10 .r10 (.imm 0),
      .cmp .r11 (.imm 0)])
    (.ite .eq (.block []) (copyLoop (w := w)))

/-! ## `update` -/

/-- Fill the buffer with `min(B - r8, r7)` bytes of `data`: `r11 := B - r8`,
and if `r7 < B` and `r7 + r8 < B` (i.e. `r7 < B - r8`), `r11 := r7`. -/
def fill : Prog isa :=
  .seq (.block [.mov .r11 (.imm (BitVec.ofNat 32 (B w))), .dp .sub .r11 .r11 (.reg .r8),
      .mov .r12 (.shifted .r7 .lsr (lbb w)), .cmp .r12 (.imm 0)])
  (.seq (.ite .eq
      (.seq (.block [.dp .add .r12 .r7 (.reg .r8), .mov .r12 (.shifted .r12 .lsr (lbb w)),
          .cmp .r12 (.imm 0)])
        (.ite .eq (.block [.mov .r11 (.reg .r7)]) (.block [])))
      (.block []))
    (copy (w := w)))

/-- The arguments of a call, but `n` (`r2`), the blocks (`r1`) and the
counter (`r3:r11`): the state, no final block flag, and `scratch`. -/
def args : List Instr := [.mov .r0 (.reg .r4), .mov .r12 (.imm 0), .mov .lr (.reg .r5)]

/-- Save the registers, set ours up, and fill a non-empty buffer; set up the
first call: the buffer, with `n` = 1 if it is full (i.e. not empty) and more
data follows, and 0 otherwise, and the byte count as its counter. -/
def updatePro : Prog isa :=
  .seq (.block ([.ldrSp .r12 8] ++ save .r12 ++ [.mov .r4 (.reg .r0), .mov .r5 (.reg .r12), .ldrSp .r6 0,
      .ldrSp .r7 4, .mov .r9 (.reg .r2), .mov .r10 (.reg .r3)]))
  (.seq (bufLen (w := w))
  (.seq (.block [.cmp .r8 (.imm 0)])
  (.seq (.ite .eq (.block []) (fill (w := w)))
  (.seq (.block [.mov .r2 (.imm 0), .cmp .r7 (.imm 0)])
  (.seq (.ite .eq (.block []) (.seq (.block [.cmp .r8 (.imm 0)])
      (.ite .eq (.block []) (.block [.mov .r2 (.imm 1)]))))
    (.block (args ++ [.dp .add .r1 .r4 (.imm (BitVec.ofNat 32 (N w))), .mov .r3 (.reg .r9),
      .mov .r11 (.reg .r10)])))))))

/-- If more data follows, the buffer is empty now; set up the second call:
the `(r7 - 1) / B` whole blocks of `data` but the last, whose first counter
is `count + B` (none if `r7 = 0`, at the state, as `data` may then end at the
end of the address space). -/
def updateMid : Prog isa :=
  .seq (.block [.cmp .r7 (.imm 0)])
  (.seq (.ite .eq (.block [.mov .r2 (.imm 0), .mov .r1 (.reg .r4)])
      (.block [.mov .r8 (.imm 0), .dp .sub .r2 .r7 (.imm 1), .mov .r2 (.shifted .r2 .lsr (lbb w)),
        .mov .r1 (.reg .r6)]))
    (.block (args ++ [.adds .r3 .r9 (.imm (BitVec.ofNat 32 (B w))), .adc .r11 .r10 (.imm 0)])))

/-- If data is left, skip the `r7 - ((r7 - 1) mod B + 1)` bytes compressed,
and copy the rest (1 to `B` bytes) to the (empty) buffer; then restore the
registers. -/
def updateEnd : Prog isa :=
  .seq (.block [.cmp .r7 (.imm 0)])
  (.seq (.ite .eq (.block [])
      (.seq (.block [.dp .sub .r11 .r7 (.imm 1), .dp .and .r11 .r11 (.imm (BitVec.ofNat 32 (B w - 1))),
          .dp .add .r11 .r11 (.imm 1), .dp .sub .r12 .r7 (.reg .r11), .dp .add .r6 .r6 (.reg .r12),
          .dp .sub .r7 .r7 (.reg .r12), .adds .r9 .r9 (.reg .r12), .adc .r10 .r10 (.imm 0)])
        (copy (w := w))))
    (.block restore))

def update (name : String) (code : Prog isa) : Prog isa :=
  .seq (updatePro (w := w)) (.seq (call name code) (.seq (updateMid (w := w))
    (.seq (call name code) (updateEnd (w := w)))))

/-! ## `finalize` -/

/-- The loop zeroing the buffer from byte `r8` on, `r11 ≥ 1` bytes (`r12 = 0`). -/
def zeroLoop : Prog isa :=
  .loop (.block [.dp .add .r1 .r4 (.reg .r8), .strb .r12 .r1 (N w), .dp .add .r8 .r8 (.imm 1),
    .subs .r11 .r11 (.imm 1)]) .ne

/-- Save the registers, set ours up, zero the rest of the buffer, and set up
the call: the buffer, as the last block, with the byte count as its
counter. -/
def finalizePro : Prog isa :=
  .seq (.block ([.ldrSp .r12 4] ++ save .r12 ++ [.mov .r4 (.reg .r0), .mov .r5 (.reg .r12), .ldrSp .r6 0,
      .mov .r9 (.reg .r2), .mov .r10 (.reg .r3)]))
  (.seq (bufLen (w := w))
  (.seq (.block [.mov .r12 (.imm 0), .mov .r11 (.imm (BitVec.ofNat 32 (B w))), .subs .r11 .r11 (.reg .r8)])
  (.seq (.ite .eq (.block []) (zeroLoop (w := w)))
    (.block [.mov .r0 (.reg .r4), .dp .add .r1 .r4 (.imm (BitVec.ofNat 32 (N w))), .mov .r2 (.imm 1),
      .mov .r3 (.reg .r9), .mov .r11 (.reg .r10), .mov .r12 (.imm 1), .mov .lr (.reg .r5)]))))

/-- Copy the hash value (at `r4`) to `out` (at `r6`), and restore the registers. -/
def finalizeEnd : List Instr :=
  (List.range (N w / 4)).flatMap (fun k => [.ldr .r12 .r4 (4 * k), .str .r12 .r6 (4 * k)]) ++ restore

def finalize (name : String) (code : Prog isa) : Prog isa :=
  .seq (finalizePro (w := w)) (.seq (call name code) (.block (finalizeEnd (w := w))))

end

/-! ## `init`

Uses only `r0`–`r3` and `r12`. -/

section
variable {w : Nat} (P : Spec.Blake2.Params w)

/-- 32-bit word `j` of the IV, stored little-endian: word `j / (ws / 4)` of
it, or its half `j mod 2` for 64-bit words. -/
def ivWord (j : Nat) : BitVec 32 :=
  ((P.IV.toList.getD (j / (ws w / 4)) 0) >>> (32 * (j % (ws w / 4)))).setWidth 32

/-- `r12 := v` -/
def movImm (v : BitVec 32) : List Instr :=
  [.movw .r12 (v.extractLsb' 0 16), .movt .r12 (v.extractLsb' 16 16)]

/-- `h := IV`, with the parameter block `0x0101kknn` XORed into its first
word (`kk` = `keylen` in `r3`, `nn` = `outlen` in `r1`). -/
def initState : List Instr :=
  (List.range (N w / 4 - 1)).flatMap (fun j => movImm (ivWord P (j + 1)) ++ [.str .r12 .r0 (4 * (j + 1))]) ++
  movImm (ivWord P 0 ^^^ 0x01010000) ++
  [.dp .eor .r12 .r12 (.shifted .r3 .lsl 8), .dp .eor .r12 .r12 (.reg .r1), .str .r12 .r0 0]

/-- Zero the buffer and copy the `r3 ≥ 1` bytes of the key (at `r2`) to it. -/
def keyBlock : Prog isa :=
  .seq (.block (.mov .r12 (.imm 0) :: (List.range (B w / 4)).map (fun j => .str .r12 .r0 (N w + 4 * j)) ++
      [.dp .add .r1 .r0 (.imm (BitVec.ofNat 32 (N w)))]))
    (.loop (.block [.ldrb .r12 .r2 0, .strb .r12 .r1 0, .dp .add .r2 .r2 (.imm 1), .dp .add .r1 .r1 (.imm 1),
      .subs .r3 .r3 (.imm 1)]) .ne)

def init : Prog isa :=
  .seq (.block (initState P ++ [.cmp .r3 (.imm 0)])) (.ite .eq (.block []) (keyBlock (w := w)))

end

end VG.Impl.Blake2.Arm.Stream
