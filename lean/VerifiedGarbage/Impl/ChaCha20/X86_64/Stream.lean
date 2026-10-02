import VerifiedGarbage.Impl.ChaCha20.X86_64.Callee

/-!
# Streaming ChaCha20: x86-64 implementation

`vg_chacha20_init(state = rdi, key = rsi, nonce = rdx)`,
`vg_chacha20_set_nonce(state = rdi, nonce = rsi)` and
`vg_chacha20_apply(state = rdi, data = rsi, len = rdx) -> eax`, on the
streaming state of `VG.Spec.ChaCha20.restAt` (768 bytes):

* `[0, 64)`: the 16-word state, `[64, 128)`: the buffered block,
  `[128, 136)`: the number of bytes of keystream left;
* `[192, 256)`: the copy of the 16-word state that `vg_chacha20_xor` is
  given (it leaves its state unspecified), `[256, 576)`: its working space;
* `[576, 600)`: our caller's `rbx, rbp, r12`; `[600, 608)`: the number of
  bytes left after `apply`, stored there first since the block function
  overwrites `[64, 320)`.

`set_nonce` writes the constants, the nonce (words 12–15) and the number of
bytes left, 64 × (2³² − c) for the initial block counter `c`; `init` also
copies the key, then does the same.

`apply` returns 0 at once if fewer than `len` bytes are left. Otherwise it
XORs the bytes left in the buffered block (the last `left % 64`, as many as
`len` asks for), then the whole blocks that follow with `vg_chacha20_xor`
(an implementation `x` of it: `apply` is generic over them), advancing the
counter, and finally, if bytes remain, computes the next block into the
buffer with `vg_chacha20_block`, advances the counter and XORs its first
bytes. `rbx` holds the state, `rbp` the data not yet processed and `r12` its
length throughout, which the callees preserve.

The branches are on the length and the number of bytes left only, and every
address is a pointer plus a constant, those two or a count: only the
pointers, the length and the number of bytes left (which the contract lets
`apply` leak) can affect timing.
-/

namespace VG.Impl.ChaCha20.X86_64.Stream

open VG.X86_64
open VG.Impl.ChaCha20.X86_64 (at_ block)
open VG.Impl.ChaCha20.X86_64.Xor (xorLoop)

/-- The nonce at `rsi`, the constants and the number of bytes left, into
the state at `rdi`. -/
def setNonceInstrs : List Instr :=
  [.mov .rax (.mem (at_ .rsi 0)), .mov .rcx (.mem (at_ .rsi 8)), .mov32 .rdx (.mem (at_ .rsi 0)),
   .store (at_ .rdi 48) .rax, .store (at_ .rdi 56) .rcx,
   .movImm64 .rax 0x3320646e61707865, .store (at_ .rdi 0) .rax,
   .movImm64 .rax 0x6b20657479622d32, .store (at_ .rdi 8) .rax,
   .movImm64 .rcx 0x100000000, .alu .sub .rcx (.reg .rdx),
   .alu .add .rcx (.reg .rcx), .alu .add .rcx (.reg .rcx), .alu .add .rcx (.reg .rcx),
   .alu .add .rcx (.reg .rcx), .alu .add .rcx (.reg .rcx), .alu .add .rcx (.reg .rcx),
   .store (at_ .rdi 128) .rcx]

def setNonce : Prog isa := .block setNonceInstrs

/-- The key at `rsi` into words 4–11, and the nonce pointer into `rsi`. -/
def keyInstrs : List Instr :=
  [.mov .rax (.mem (at_ .rsi 0)), .mov .rcx (.mem (at_ .rsi 8)), .mov .r8 (.mem (at_ .rsi 16)),
   .mov .r9 (.mem (at_ .rsi 24)), .store (at_ .rdi 16) .rax, .store (at_ .rdi 24) .rcx,
   .store (at_ .rdi 32) .r8, .store (at_ .rdi 40) .r9, .mov .rsi (.reg .rdx)]

def init : Prog isa := .block (keyInstrs ++ setNonceInstrs)

/-! ## `apply` -/

/-- `rax` = the bytes left; the carry is set iff fewer than `len`. -/
def check : List Instr := [.mov .rax (.mem (at_ .rdi 128)), .alu .cmp .rax (.reg .rdx)]

/-- Saves our caller's registers, stores the bytes left after `apply`, and
computes `rax` = the bytes left in the buffered block; `rdx` = `len`, and
the carry is set iff `rax < len`. -/
def start : List Instr :=
  [.store (at_ .rdi 576) .rbx, .store (at_ .rdi 584) .rbp, .store (at_ .rdi 592) .r12,
   .mov .rbx (.reg .rdi), .mov .rbp (.reg .rsi), .mov .r12 (.reg .rdx),
   .mov .rcx (.reg .rax), .alu .sub .rcx (.reg .rdx), .store (at_ .rbx 600) .rcx,
   .alu .and .rax (.imm 63), .alu .cmp .rax (.reg .rdx)]

/-- XORs the `rdx` bytes at `rsi` into the data (`rbp`), and moves past them. -/
def xorBytes : Prog isa :=
  .seq (.block [.mov32 .rcx (.imm 0), .alu .test .rdx (.reg .rdx)])
  (.seq (.ite .e (.block []) xorLoop)
    (.block [.alu .add .rbp (.reg .rdx), .alu .sub .r12 (.reg .rdx)]))

/-- Everything up to the call of `vg_chacha20_xor`: the bytes left in the
buffered block, `rdx = min(rax, len)` of them, from `rbx + 128 - rax`; then
`rdx` = the bytes of the whole blocks that follow (`r12` rounded down to a
multiple of 64), with the zero flag set iff there are none. -/
def part1 : Prog isa :=
  .seq (.block start)
  (.seq (.ite .b (.block [.mov .rdx (.reg .rax)]) (.block []))
  (.seq (.block [.mov .rsi (.reg .rbx), .alu .add .rsi (.imm 128), .alu .sub .rsi (.reg .rax)])
  (.seq xorBytes
    (.block [.mov .rdx (.reg .r12), .alu .and .rdx (.imm 0xffffffc0)]))))

/-- The whole blocks: the state copied and the counter advanced, then
`vg_chacha20_xor` (`x`) on the copy. -/
def blocksArgs : List Instr :=
  [.mov .rax (.mem (at_ .rbx 0)), .store (at_ .rbx 192) .rax,
   .mov .rax (.mem (at_ .rbx 8)), .store (at_ .rbx 200) .rax,
   .mov .rax (.mem (at_ .rbx 16)), .store (at_ .rbx 208) .rax,
   .mov .rax (.mem (at_ .rbx 24)), .store (at_ .rbx 216) .rax,
   .mov .rax (.mem (at_ .rbx 32)), .store (at_ .rbx 224) .rax,
   .mov .rax (.mem (at_ .rbx 40)), .store (at_ .rbx 232) .rax,
   .mov .rax (.mem (at_ .rbx 48)), .store (at_ .rbx 240) .rax,
   .mov .rax (.mem (at_ .rbx 56)), .store (at_ .rbx 248) .rax,
   .mov .rcx (.reg .rdx), .shift .shr .rcx 6, .mov32 .rax (.mem (at_ .rbx 48)),
   .alu32 .add .rax (.reg .rcx), .store32 (at_ .rbx 48) .rax,
   .mov .rdi (.reg .rbx), .alu .add .rdi (.imm 192), .mov .rsi (.reg .rbp),
   .mov .rcx (.reg .rbx), .alu .add .rcx (.imm 256),
   .alu .add .rbp (.reg .rdx), .alu .sub .r12 (.reg .rdx)]

def part2 (x : Callee) : Prog isa :=
  .ite .e (.block []) (.seq (.block blocksArgs) (.call x.name x.code))

/-- The arguments of the block function: the state and the buffer. -/
def tailArgs : List Instr := [.mov .rdi (.reg .rbx), .mov .rsi (.reg .rbx), .alu .add .rsi (.imm 64)]

/-- After the block function: the counter advanced, and `r12` bytes of the
block XORed. -/
def tailXor : Prog isa :=
  .seq (.block [.mov32 .rax (.mem (at_ .rbx 48)), .alu32 .add .rax (.imm 1),
    .store32 (at_ .rbx 48) .rax, .mov .rsi (.reg .rbx), .alu .add .rsi (.imm 64),
    .mov .rdx (.reg .r12)])
    xorBytes

/-- The last bytes, if any: the next block into the buffer, the counter
advanced, and `r12` bytes of the block XORed. -/
def part3 : Prog isa :=
  .seq (.block [.alu .test .r12 (.reg .r12)])
  (.ite .e (.block [])
    (.seq (.block tailArgs) (.seq (.call "vg_chacha20_block" block) tailXor)))

/-- The bytes left stored, our caller's registers restored, and 1 returned. -/
def finish : List Instr :=
  [.mov .rax (.mem (at_ .rbx 600)), .store (at_ .rbx 128) .rax,
   .mov .rbp (.mem (at_ .rbx 584)), .mov .r12 (.mem (at_ .rbx 592)), .mov .rbx (.mem (at_ .rbx 576)),
   .mov32 .rax (.imm 1)]

def apply (x : Callee) : Prog isa :=
  .seq (.block check)
  (.ite .b (.block [.mov32 .rax (.imm 0)])
    (.seq part1 (.seq (part2 x) (.seq part3 (.block finish)))))

end VG.Impl.ChaCha20.X86_64.Stream
