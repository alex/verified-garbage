import VerifiedGarbage.Impl.Rc2.X86.Cbc
import VerifiedGarbage.Impl.Rc2.X86.ExpandKey

/-! # Streaming RC2-CBC on baseline x86

Every argument is on the stack (cdecl), argument `i` at `[esp + 4 + 4i]`.

`vg_rc2_cbc_init(key, key_len, effective_bits, iv, iv_len, ctx, scratch)`
checks the lengths, leaving in `eax` 1, 2 or 3 for the first that is
invalid, or 0. If they are valid, it copies the IV to `ctx + 128` and calls
`vg_rc2_expand_key(key, key_len, effective_bits, ctx, scratch)` to write the
schedule to `ctx`, and returns 0.

`vg_rc2_cbc_{en,de}crypt_update(ctx, pending_len, data, len, out, out_len,
scratch)`: if `out_len` is 0, it appends the data to the pending bytes at
`ctx + 136 + pending_len`. Otherwise it copies the pending bytes and the
first `out_len - pending_len` bytes of data to `out`, the rest of the data to
`ctx + 136`, and calls the CBC function on the `out_len / 8` blocks at `out`,
with the schedule at `ctx` and the chaining value at `ctx + 128`.

Each call pushes its five arguments in a frame of their own (`scratch` =
`ebx`, then `esi`, `edx`, `ecx`, `eax`), popped (into `eax`) when it
returns, so `ebx` and `esi` hold arguments: our caller's values of them are
saved in `scratch[512..520)`, beyond the callee's scratch space, and
restored after the call through `ebx`, which the callee preserves. Bytes are
copied one at a time from `esi` to `edx`, `ecx` of them, through `al`. Every
branch, loop count and address depends only on `esp`, the pointers and the
lengths.
-/

namespace VG.Impl.Rc2.X86.Stream

open VG.X86

/-- Argument `i`, `[esp + 4 + 4i]`. -/
def argOp (i : Nat) : MemOp := memOp .esp (4 + 4 * i)

/-- One byte from `[esi + sd]` to `[edx + dd]`; ZF is set once `ecx` reaches 0. -/
def copyBody (sd dd : Nat) : List Instr :=
  [.movzx8 .eax (memOp .esi sd), .store8 (memOp .edx dd) .al, .alu .add .esi (.imm 1),
   .alu .add .edx (.imm 1), .alu .sub .ecx (.imm 1)]

/-- Copies `ecx` bytes from `esi + sd` to `edx + dd`, advancing `esi` and `edx`. -/
def copy (sd dd : Nat) : Prog isa :=
  .seq (.block [.alu .test .ecx (.reg .ecx)]) (.ite .e (.block []) (.loop (.block (copyBody sd dd)) .ne))

/-- Saves our caller's `ebx` and `esi` in `scratch[512..520)`, with `scratch` in `eax`. -/
def save : List Instr :=
  [.mov .eax (.mem (argOp 6)), .store (memOp .eax 512) .ebx, .store (memOp .eax 516) .esi]

/-- Restores them, with `scratch` in `ebx`. -/
def restore : List Instr :=
  [.mov .esi (.mem (memOp .ebx 516)), .mov .ebx (.mem (memOp .ebx 512))]

/-- A call with the arguments `eax`, `ecx`, `edx`, `esi`, `ebx`. -/
def call5 (name : String) (code : Prog isa) : Prog isa :=
  .frame (.push [.ebx, .esi, .edx, .ecx, .eax]) (.call name code) (.pop .eax 5)

/-! ## `init` -/

/-- 1 unless `key_len` is in 1..=128 (CF clear: `key_len - 1 ≥ 128`). -/
def checkKey : List Instr :=
  [imm .eax 1, .mov .ecx (.mem (argOp 1)), .alu .sub .ecx (.imm 1), .alu .cmp .ecx (.imm 128)]

/-- 2 unless `effective_bits` is in 1..=1024. -/
def checkBits : List Instr :=
  [imm .eax 2, .mov .ecx (.mem (argOp 2)), .alu .sub .ecx (.imm 1), .alu .cmp .ecx (.imm 1024)]

/-- 3 unless `iv_len` is 8. -/
def checkIv : List Instr := [imm .eax 3, .mov .ecx (.mem (argOp 4)), .alu .cmp .ecx (.imm 8)]

/-- `eax` := the error code, or 0. -/
def checks : Prog isa :=
  .seq (.block checkKey) (.ite .ae (.block [])
    (.seq (.block checkBits) (.ite .ae (.block [])
      (.seq (.block checkIv) (.ite .ne (.block []) (.block [imm .eax 0]))))))

/-- The IV to `ctx + 128`, our caller's registers saved, and the arguments of
`vg_rc2_expand_key(key, key_len, effective_bits, ctx, scratch)`. -/
def initArgs : List Instr :=
  [.mov .eax (.mem (argOp 3)), .mov .ecx (.mem (argOp 5)), .mov .edx (.mem (memOp .eax 0)),
   .store (memOp .ecx 128) .edx, .mov .edx (.mem (memOp .eax 4)), .store (memOp .ecx 132) .edx] ++
  save ++
  [rr .ebx .eax, rr .esi .ecx, .mov .edx (.mem (argOp 2)), .mov .ecx (.mem (argOp 1)),
   .mov .eax (.mem (argOp 0))]

def keyCall : Prog isa := call5 "vg_rc2_expand_key" expandKey

def initBody : Prog isa :=
  .seq (.block initArgs) (.seq keyCall (.block (restore ++ [imm .eax 0])))

def init : Prog isa :=
  .seq checks (.seq (.block [.alu .test .eax (.reg .eax)]) (.ite .ne (.block []) initBody))

/-! ## `update` -/

def cbcCall (d : Spec.Rc2.Direction) : Prog isa :=
  match d with
  | .encrypt => call5 "vg_rc2_cbc_encrypt" Cbc.encrypt
  | .decrypt => call5 "vg_rc2_cbc_decrypt" Cbc.decrypt

/-- Our caller's registers saved; ZF set if `out_len` is 0. -/
def entry : List Instr := save ++ [.mov .ecx (.mem (argOp 5)), .alu .test .ecx (.reg .ecx)]

/-- No complete block: the `len` bytes of data after the `pending_len`
pending bytes. -/
def short : Prog isa :=
  .seq (.block [.mov .esi (.mem (argOp 2)), .mov .edx (.mem (argOp 0)), .mov .ecx (.mem (argOp 1)),
      .alu .add .edx (.reg .ecx), .mov .ecx (.mem (argOp 3))])
    (copy 0 136)

/-- The `pending_len` pending bytes to `out`. -/
def toOut₁ : List Instr := [.mov .esi (.mem (argOp 0)), .mov .edx (.mem (argOp 4)), .mov .ecx (.mem (argOp 1))]

/-- `out_len - pending_len` bytes of data after them. -/
def toOut₂ : List Instr :=
  [.mov .esi (.mem (argOp 2)), .mov .ecx (.mem (argOp 5)), .mov .eax (.mem (argOp 1)),
   .alu .sub .ecx (.reg .eax)]

/-- The rest, `len - (out_len - pending_len)` bytes, to `ctx + 136`. -/
def toPending : List Instr :=
  [.mov .edx (.mem (argOp 0)), .mov .ecx (.mem (argOp 3)), .mov .eax (.mem (argOp 5)),
   .alu .sub .ecx (.reg .eax), .mov .eax (.mem (argOp 1)), .alu .add .ecx (.reg .eax)]

def long : Prog isa :=
  .seq (.block toOut₁) (.seq (copy 136 0)
    (.seq (.block toOut₂) (.seq (copy 0 0) (.seq (.block toPending) (copy 0 136)))))

/-- The arguments of the CBC function: `schedule = ctx`, `iv = ctx + 128`,
`data = out`, `n = out_len / 8`, `scratch`; ZF set if `n` is 0. -/
def cbcArgs : List Instr :=
  [.mov .ebx (.mem (argOp 6)), .mov .eax (.mem (argOp 0)), rr .ecx .eax, .alu .add .ecx (.imm 128),
   .mov .edx (.mem (argOp 4)), .mov .esi (.mem (argOp 5)), .shift .shr .esi 3]

/-- Everything before the call. -/
def head : Prog isa := .seq (.block entry) (.seq (.ite .e short long) (.block cbcArgs))

def update (d : Spec.Rc2.Direction) : Prog isa :=
  .seq head (.seq (.ite .e (.block []) (cbcCall d)) (.block restore))

def encryptUpdate : Prog isa := update .encrypt

def decryptUpdate : Prog isa := update .decrypt

end VG.Impl.Rc2.X86.Stream
