import VerifiedGarbage.Impl.Rc2.Arm.Cbc
import VerifiedGarbage.Impl.Rc2.Arm.ExpandKey

/-! # Streaming RC2-CBC on ARMv7

`vg_rc2_cbc_init(key = r0, key_len = r1, effective_bits = r2, iv = r3,
iv_len = [sp], ctx = [sp + 4], scratch = [sp + 8])` checks the lengths,
returning 1, 2 or 3 for the first that is invalid, copies the IV to
`ctx + 128` and calls `vg_rc2_expand_key(key, key_len, effective_bits,
ctx, scratch)` to write the schedule to `ctx`, and returns 0.

`vg_rc2_cbc_{en,de}crypt_update(ctx = r0, pending_len = r1, data = r2,
len = r3, out = [sp], out_len = [sp + 4], scratch = [sp + 8])`: if `out_len`
is 0, it appends the data to the pending bytes at `ctx + 136 + pending_len`.
Otherwise it copies the pending bytes and the first `out_len - pending_len`
bytes of data to `out`, the rest of the data to `ctx + 136`, and calls the
CBC function on the `out_len / 8` blocks at `out`, with the schedule at
`ctx` and the chaining value at `ctx + 128`.

Only caller-saved registers are used. The callees take their scratch buffer
on the stack: a frame pushes it (`push {r12, lr}`, the buffer in `r12` at
`[sp]`) around the call, so the functions use 8 bytes of stack. The return
address `lr`, which the code uses as a working register, is kept across the
call at `scratch + 512`, after the callees' 512 bytes of working space.

Bytes are copied one at a time, through advancing pointers (the model has
no register-offset addressing), with `r12` holding the byte. Every branch,
loop count and address depends only on the pointers and lengths.
-/

namespace VG.Impl.Rc2.Arm.Stream

open VG.Arm

/-- One byte from `[src + so]` to `[dst + dd]`, advancing both pointers;
`Z` is set once `cnt`, counting down, reaches 0. -/
def copyBody (src : Reg) (so : Nat) (dst : Reg) (dd : Nat) (cnt : Reg) : List Instr :=
  [.ldrb .r12 src so, .strb .r12 dst dd, .dp .add src src (.imm 1), .dp .add dst dst (.imm 1),
   .subs cnt cnt (.imm 1)]

/-- Copies `cnt` bytes from `src + so` to `dst + dd`. -/
def copy (src : Reg) (so : Nat) (dst : Reg) (dd : Nat) (cnt : Reg) : Prog isa :=
  .seq (.block [.cmp cnt (.imm 0)])
    (.ite .eq (.block []) (.loop (.block (copyBody src so dst dd cnt)) .ne))

/-- `lr` to `scratch + 512`. -/
def saveLr : List Instr := [.ldrSp .r12 8, .str .lr .r12 512]

/-- `lr` back from `scratch + 512`. -/
def restoreLr : List Instr := [.ldrSp .r12 8, .ldr .lr .r12 512]

/-! ## `init` -/

def keyCall : Prog isa :=
  .frame (.push [.r12, .lr]) (.call "vg_rc2_expand_key" expandKey) (.pop .r12 8)

/-- The IV to `ctx + 128`, and the arguments of `vg_rc2_expand_key`:
`schedule = ctx` in `r3`, `scratch` in `r12`. -/
def initArgs : List Instr :=
  saveLr ++ [.ldr .lr .r3 0, .ldr .r3 .r3 4, .ldrSp .r12 4, .str .lr .r12 128, .str .r3 .r12 132,
    .mov .r3 (.reg .r12), .ldrSp .r12 8]

def initBody : Prog isa :=
  .seq (.block initArgs) (.seq keyCall (.block (restoreLr ++ [.mov .r0 (.imm 0)])))

/-- `Z` is clear unless `key_len` is in 1..=128 (`(key_len - 1) >> 7 = 0`). -/
def checkKey : List Instr :=
  [.dp .sub .r12 .r1 (.imm 1), .mov .r12 (.shifted .r12 .lsr 7), .cmp .r12 (.imm 0)]

/-- `Z` is clear unless `effective_bits` is in 1..=1024. -/
def checkBits : List Instr :=
  [.dp .sub .r12 .r2 (.imm 1), .mov .r12 (.shifted .r12 .lsr 10), .cmp .r12 (.imm 0)]

/-- `Z` is clear unless `iv_len` is 8. -/
def checkIv : List Instr := [.ldrSp .r12 0, .cmp .r12 (.imm 8)]

/-- The checks: `r0` is the error code of the first that fails, and `Z` is
set if none does. -/
def checks : Prog isa :=
  .seq (.block checkKey) (.ite .ne (.block [.mov .r0 (.imm 1)])
    (.seq (.block checkBits) (.ite .ne (.block [.mov .r0 (.imm 2)])
      (.seq (.block checkIv) (.ite .ne (.block [.mov .r0 (.imm 3)]) (.block []))))))

def init : Prog isa :=
  .seq checks (.ite .ne (.block []) initBody)

/-! ## `update` -/

def cbcCall (d : Spec.Rc2.Direction) : Prog isa :=
  .frame (.push [.r12, .lr])
    (match d with
      | .encrypt => .call "vg_rc2_cbc_encrypt" Cbc.encrypt
      | .decrypt => .call "vg_rc2_cbc_decrypt" Cbc.decrypt)
    (.pop .r12 8)

/-- No complete block: the data after the pending bytes. -/
def short : Prog isa :=
  .seq (.block [.dp .add .r1 .r0 (.reg .r1)]) (copy .r2 0 .r1 136 .r3)

/-- The pending bytes go to `lr = out`, from `r0 + 136 = ctx + 136`. -/
def toOut : List Instr := saveLr ++ [.ldrSp .lr 0]

/-- After them (`r0 = ctx + p`, `lr = out + p`): `r12 = p`, `r0 = ctx`,
`r1 = out_len - p` bytes of data to `lr`, and `r3 = len - r1` bytes left. -/
def middle : List Instr :=
  [.ldrSp .r12 0, .dp .sub .r12 .lr (.reg .r12), .dp .sub .r0 .r0 (.reg .r12), .ldrSp .r1 4,
   .dp .sub .r1 .r1 (.reg .r12), .dp .sub .r3 .r3 (.reg .r1)]

/-- The rest, `r3` bytes from `r2`, go to `lr + 136 = ctx + 136`. -/
def toPending : List Instr := [.mov .lr (.reg .r0)]

/-- The arguments of the CBC function: `schedule = ctx`, `iv = ctx + 128`,
`data = out`, `n = out_len / 8`, and `scratch` in `r12` for the frame. -/
def cbcArgs : List Instr :=
  [.dp .add .r1 .r0 (.imm 128), .ldrSp .r2 0, .ldrSp .r3 4, .mov .r3 (.shifted .r3 .lsr 3),
   .ldrSp .r12 8]

def long (d : Spec.Rc2.Direction) : Prog isa :=
  .seq (.block toOut)
    (.seq (copy .r0 136 .lr 0 .r1)
      (.seq (.block middle)
        (.seq (copy .r2 0 .lr 0 .r1)
          (.seq (.block toPending)
            (.seq (copy .r2 0 .lr 136 .r3)
              (.seq (.block cbcArgs) (.seq (cbcCall d) (.block restoreLr))))))))

def update (d : Spec.Rc2.Direction) : Prog isa :=
  .seq (.block [.ldrSp .r12 4, .cmp .r12 (.imm 0)]) (.ite .eq short (long d))

def encryptUpdate : Prog isa := update .encrypt

def decryptUpdate : Prog isa := update .decrypt

end VG.Impl.Rc2.Arm.Stream
