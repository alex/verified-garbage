import VerifiedGarbage.Impl.Rc2.AArch64.Cbc
import VerifiedGarbage.Impl.Rc2.AArch64.ExpandKey

/-! # Streaming RC2-CBC on baseline AArch64

`vg_rc2_cbc_init(key = x0, key_len = x1, effective_bits = x2, iv = x3,
iv_len = x4, ctx = x5, scratch = x6)` checks the lengths, returning 1, 2 or 3
in `x0` for the first that is invalid, copies the IV to `ctx + 128` and calls
`vg_rc2_expand_key` to write the schedule to `ctx`, and returns 0.

`vg_rc2_cbc_{en,de}crypt_update(ctx = x0, pending_len = x1, data = x2,
len = x3, out = x4, out_len = x5, scratch = x6)`: if `out_len` is 0, it
appends the data to the pending bytes at `ctx + 136 + pending_len`.
Otherwise it copies the pending bytes and the first `out_len - pending_len`
bytes of data to `out`, the rest of the data to `ctx + 136`, and calls the
CBC function on the `out_len / 8` blocks at `out`, with the schedule at
`ctx` and the chaining value at `ctx + 128`.

Nothing is kept across a call, which is last, so only caller-saved registers
are used; the return address (`x30`), which the call replaces, is saved in a
16-byte stack frame around the code that calls.

The model has no flags and no register-offset addressing: the range checks
are a subtraction and a shift tested with `cbz`/`cbnz`, and bytes are copied
one at a time (`copy`) through pointers that advance, `x9` holding the byte.
Every branch, loop count and address depends only on the pointers and
lengths.
-/

namespace VG.Impl.Rc2.AArch64.Stream

open VG.AArch64

/-- `mov d, n` (as `add d, n, #0`). -/
def mov (d n : Reg) : Instr := .addImm .x d n 0

/-- One byte from `[src + so]` to `[dst + dd]`, advancing both pointers and
counting `cnt` down. -/
def copyBody (src : Reg) (so : Nat) (dst : Reg) (dd : Nat) (cnt : Reg) : List Instr :=
  [.ldrb .x9 src so, .strb .x9 dst dd, .addImm .x src src 1, .addImm .x dst dst 1,
    .subImm .x cnt cnt 1]

/-- Copies `cnt` bytes from `src + so` to `dst + dd`; afterwards `src` and
`dst` have advanced by the count and `cnt` is 0. -/
def copy (src : Reg) (so : Nat) (dst : Reg) (dd : Nat) (cnt : Reg) : Prog isa :=
  .ite (.zero .x cnt) (.block [])
    (.loop (.block (copyBody src so dst dd cnt)) (.nonzero .x cnt))

/-! ## `init` -/

def keyCall : Prog isa := .call "vg_rc2_expand_key" expandKey

/-- The IV to `ctx + 128`, and the arguments of `vg_rc2_expand_key`:
`schedule = ctx`, `scratch`. -/
def initArgs : List Instr :=
  [.ldr .x .x8 .x3 0, .str .x .x8 .x5 128, mov .x3 .x5, mov .x4 .x6]

/-- The IV, the key schedule, and 0, inside the frame saving `x30`. -/
def initMain : Prog isa :=
  .seq (.block initArgs) (.seq keyCall (.block [.movz .x .x0 0 0]))

/-- `x8 ≠ 0` unless `key_len` is in 1..=128: `(key_len - 1) >> 7`. -/
def checkKey : List Instr := [.subImm .x .x8 .x1 1, .lsr .x .x8 .x8 7]

/-- `x8 ≠ 0` unless `effective_bits` is in 1..=1024. -/
def checkBits : List Instr := [.subImm .x .x8 .x2 1, .lsr .x .x8 .x8 10]

/-- `x8 ≠ 0` unless `iv_len` is 8. -/
def checkIv : List Instr := [.subImm .x .x8 .x4 8]

def init : Prog isa :=
  .seq (.block checkKey) (.ite (.nonzero .x .x8) (.block [.movz .x .x0 1 0])
    (.seq (.block checkBits) (.ite (.nonzero .x .x8) (.block [.movz .x .x0 2 0])
      (.seq (.block checkIv) (.ite (.nonzero .x .x8) (.block [.movz .x .x0 3 0])
        (.frame (.push .x30) initMain (.pop .x30)))))))

/-! ## `update` -/

def cbcCall (d : Spec.Rc2.Direction) : Prog isa :=
  match d with
  | .encrypt => .call "vg_rc2_cbc_encrypt" Cbc.encrypt
  | .decrypt => .call "vg_rc2_cbc_decrypt" Cbc.decrypt

/-- No complete block: the data after the pending bytes. -/
def short : Prog isa :=
  .seq (.block [.add .x .x8 .x0 .x1]) (copy .x2 0 .x8 136 .x3)

/-- The pending bytes (`x1` of them, from `x10 = ctx`) go to `x11 = out`. -/
def toOut : List Instr := [mov .x10 .x0, mov .x11 .x4, mov .x12 .x1]

/-- Then `x12 = out_len - pending_len` bytes of data go after them. -/
def toOutData : List Instr := [.sub .x .x12 .x5 .x1]

/-- The rest, `x3 = len + pending_len - out_len` bytes, go to `x10 = ctx`
(at `ctx + 136`). -/
def toPending : List Instr := [.add .x .x3 .x3 .x1, .sub .x .x3 .x3 .x5, mov .x10 .x0]

/-- The arguments of the CBC function: `schedule = ctx`, `iv = ctx + 128`,
`data = out`, `n = out_len / 8`, `scratch`. -/
def cbcArgs : List Instr := [.addImm .x .x1 .x0 128, mov .x2 .x4, .lsr .x .x3 .x5 3, mov .x4 .x6]

/-- The copies, and the arguments of the CBC function. -/
def prep : Prog isa :=
  .seq (.block toOut)
    (.seq (copy .x10 136 .x11 0 .x12)
      (.seq (.block toOutData)
        (.seq (copy .x2 0 .x11 0 .x12)
          (.seq (.block toPending)
            (.seq (copy .x2 0 .x10 136 .x3) (.block cbcArgs))))))

/-- With complete blocks, inside the frame saving `x30`. -/
def longMain (d : Spec.Rc2.Direction) : Prog isa := .seq prep (cbcCall d)

def update (d : Spec.Rc2.Direction) : Prog isa :=
  .ite (.zero .x .x5) short (.frame (.push .x30) (longMain d) (.pop .x30))

def encryptUpdate : Prog isa := update .encrypt

def decryptUpdate : Prog isa := update .decrypt

end VG.Impl.Rc2.AArch64.Stream
