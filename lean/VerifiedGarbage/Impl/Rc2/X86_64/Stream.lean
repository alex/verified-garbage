import VerifiedGarbage.Impl.Rc2.X86_64.Cbc
import VerifiedGarbage.Impl.Rc2.X86_64.ExpandKey

/-! # Streaming RC2-CBC on baseline x86-64

`vg_rc2_cbc_init(key = rdi, key_len = rsi, effective_bits = rdx, iv = rcx,
iv_len = r8, ctx = r9, scratch = [rsp + 8])` checks the lengths, returning
1, 2 or 3 for the first that is invalid; otherwise it copies the IV to `ctx + 128` and
calls `vg_rc2_expand_key` to write the schedule to `ctx`, and returns 0.

`vg_rc2_cbc_{en,de}crypt_update(ctx = rdi, pending_len = rsi, data = rdx,
len = rcx, out = r8, out_len = r9, scratch = [rsp + 8])`: if `out_len` is 0,
it appends the data to the pending bytes at `ctx + 136 + pending_len`.
Otherwise it copies the pending bytes and the first `out_len - pending_len`
bytes of data to `out`, the rest of the data to `ctx + 136`, and calls the
CBC function on the `out_len / 8` blocks at `out`, with the schedule at
`ctx` and the chaining value at `ctx + 128`. Nothing is kept across the
call, which is last, so only caller-saved registers are used.

Bytes are copied one at a time, with `r10` as the index and `r11` holding
the byte. Every branch, loop count and address depends only on the
pointers and lengths; the scratch pointer is loaded last before each call.
-/

namespace VG.Impl.Rc2.X86_64.Stream

open VG.X86_64

/-- `[base + r10 + disp]`. -/
def at10 (base : Reg) (disp : Nat) : MemOp := { base, index := some .r10, disp := Int.ofNat disp }

/-- One byte from `[src + r10 + sd]` to `[dst + r10 + dd]`; ZF is set once
`r10` reaches `cnt`. -/
def copyBody (src : Reg) (sd : Nat) (dst : Reg) (dd : Nat) (cnt : Reg) : List Instr :=
  [.movzx8 .r11 (at10 src sd), .store8 (at10 dst dd) .r11, .alu .add .r10 (.imm 1),
   .alu .cmp .r10 (.reg cnt)]

/-- Copies `cnt` bytes from `src + sd` to `dst + dd`. -/
def copy (src : Reg) (sd : Nat) (dst : Reg) (dd : Nat) (cnt : Reg) : Prog isa :=
  .seq (.block [.mov32 .r10 (.imm 0), .alu .test cnt (.reg cnt)])
    (.ite .e (.block []) (.loop (.block (copyBody src sd dst dd cnt)) .ne))

/-! ## `init` -/

def keyCall : Prog isa := .call "vg_rc2_expand_key" expandKey

/-- The IV to `ctx + 128`, and the arguments of `vg_rc2_expand_key`:
`schedule = ctx`, `scratch` from the stack. -/
def initArgs : List Instr :=
  [.mov .rax (.mem (memOp .rcx 0)), .store (memOp .r9 128) .rax, rr .rcx .r9,
   .mov .r8 (.mem (memOp .rsp 8))]

def initBody : Prog isa :=
  .seq (.block initArgs) (.seq keyCall (.block [.mov32 .rax (.imm 0)]))

/-- 1 unless `key_len` is in 1..=128 (CF clear: `key_len - 1 ≥ 128`). -/
def checkKey : List Instr :=
  [.mov32 .rax (.imm 1), rr .r10 .rsi, .alu .sub .r10 (.imm 1), .alu .cmp .r10 (.imm 128)]

/-- 2 unless `effective_bits` is in 1..=1024. -/
def checkBits : List Instr :=
  [.mov32 .rax (.imm 2), rr .r10 .rdx, .alu .sub .r10 (.imm 1), .alu .cmp .r10 (.imm 1024)]

/-- 3 unless `iv_len` is 8. -/
def checkIv : List Instr := [.mov32 .rax (.imm 3), .alu .cmp .r8 (.imm 8)]

/-- The return code in `rax`: 1, 2 or 3 for the first invalid length, else 0;
then ZF is set iff it is 0. -/
def checks : Prog isa :=
  .seq (.seq (.block checkKey) (.ite .ae (.block [])
    (.seq (.block checkBits) (.ite .ae (.block [])
      (.seq (.block checkIv) (.ite .ne (.block []) (.block [.mov32 .rax (.imm 0)])))))))
    (.block [.alu .test .rax (.reg .rax)])

def init : Prog isa := .seq checks (.ite .ne (.block []) initBody)

/-! ## `update` -/

def cbcCall (d : Spec.Rc2.Direction) : Prog isa :=
  match d with
  | .encrypt => .call "vg_rc2_cbc_encrypt" Cbc.encrypt
  | .decrypt => .call "vg_rc2_cbc_decrypt" Cbc.decrypt

/-- No complete block: the data after the pending bytes. -/
def short : Prog isa :=
  .seq (.block [rr .rax .rdi, .alu .add .rax (.reg .rsi)]) (copy .rdx 0 .rax 136 .rcx)

/-- `r9 = out_len - pending_len` bytes of data go to `r8 = out + pending_len`. -/
def toOut : List Instr := [.alu .sub .r9 (.reg .rsi), .alu .add .r8 (.reg .rsi)]

/-- The rest, `rcx = len - r9` bytes from `rdx = data + r9`, go to `ctx + 136`. -/
def toPending : List Instr := [.alu .add .rdx (.reg .r9), .alu .sub .rcx (.reg .r9)]

/-- The arguments of the CBC function: `schedule = ctx`, `iv = ctx + 128`,
`data = out`, `n = out_len / 8`, `scratch` from the stack. -/
def cbcArgs : List Instr :=
  [.alu .sub .r8 (.reg .rsi), .alu .add .r9 (.reg .rsi), .shift .shr .r9 3, rr .rdx .r8,
   rr .rcx .r9, rr .rsi .rdi, .alu .add .rsi (.imm 128), .mov .r8 (.mem (memOp .rsp 8))]

/-- Everything before the call of the CBC function. -/
def longPre : Prog isa :=
  .seq (copy .rdi 136 .r8 0 .rsi)
    (.seq (.block toOut)
      (.seq (copy .rdx 0 .r8 0 .r9)
        (.seq (.block toPending)
          (.seq (copy .rdx 0 .rdi 136 .rcx) (.block cbcArgs)))))

def long (d : Spec.Rc2.Direction) : Prog isa := .seq longPre (cbcCall d)

def update (d : Spec.Rc2.Direction) : Prog isa :=
  .seq (.block [.alu .test .r9 (.reg .r9)]) (.ite .e short (long d))

def encryptUpdate : Prog isa := update .encrypt

def decryptUpdate : Prog isa := update .decrypt

end VG.Impl.Rc2.X86_64.Stream
