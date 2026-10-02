import VerifiedGarbage.Impl.ChaCha20.X86.Xor

/-!
# Streaming ChaCha20: x86 (32-bit) implementation

`vg_chacha20_init(state, key, nonce)`, `vg_chacha20_set_nonce(state, nonce)`
and `vg_chacha20_apply(state, data, len) -> eax`, cdecl: the arguments are
at `[esp + 4]`, `[esp + 8]`, …. The streaming state of
`VG.Spec.ChaCha20.restAt` (768 bytes):

* `[0, 64)`: the 16-word state, `[64, 128)`: the buffered block,
  `[128, 136)`: the number of bytes of keystream left (64 bits, low word
  first);
* `[192, 256)`: the copy of the 16-word state that `vg_chacha20_xor` is
  given (it leaves its state unspecified), `[256, 576)`: its working space;
* `[576, 592)`: our caller's `ebx, esi, edi, ebp`; `[600, 608)`: the number
  of bytes left after `apply`, stored there first since the block function
  overwrites `[64, 320)`.

`set_nonce` loads everything it needs first (the nonce into `xmm0`, and the
number of bytes left, 64 × (2³² − c) for the initial block counter `c`,
computed in `edx:ecx` by doubling, as the model has no left shift), then
stores the nonce (words 12–15), the number of bytes left and the constants;
`init` also loads the key into `xmm1` and `xmm2` first, and stores it.

`apply` subtracts `len` from the number of bytes left (`sub`, `sbb`): the
borrow says whether fewer than `len` are left, and if so it returns 0 at
once. Otherwise it XORs the bytes left in the buffered block (the last
`left % 64`, as many as `len` asks for), then the whole blocks that follow
with `vg_chacha20_xor`, advancing the counter, and finally, if bytes remain,
computes the next block into the buffer with `vg_chacha20_block`, advances
the counter and XORs its first bytes. `ebx` holds the state, `esi` the data
not yet processed and `ebp` its length throughout, and `edi` the length of
the whole blocks across the call of `vg_chacha20_xor`: they are callee-saved,
so the callees keep them. Each call pushes its arguments in a frame of its
own, popped (into `eax`) when it returns: with its return address and the
12 bytes `vg_chacha20_xor` uses below its own, `apply` uses 32 bytes of
stack below its return address.

The branches are on the length and the number of bytes left only, and every
address is `esp`, a pointer plus a constant, or advances by one: only the
pointers, the length and the number of bytes left (which the contract lets
`apply` leak) can affect timing. (The argument slots may be written, so the
state pointer is loaded in a block of its own: the proof of constant time
takes it from the correctness proof, not from the slot.)
-/

namespace VG.Impl.ChaCha20.X86.Stream

open VG.X86
open VG.Impl.ChaCha20.X86 (at_ block)
open VG.Impl.ChaCha20.X86.Xor (xorLoop)

/-- `r + k` into `d`. -/
def ptr (d r : Reg) (k : Nat) : List Instr := [.mov d (.reg r), .alu .add d (.imm (BitVec.ofNat 32 k))]

/-- With the nonce pointer in `edx`: the nonce into `xmm0`, and the number
of bytes left, 64 × (2³² − c), into `edx:ecx`. -/
def nonceLoads : List Instr :=
  [.movdquLoad .xmm0 (at_ .edx 0), .mov .ecx (.imm 0), .alu .sub .ecx (.mem (at_ .edx 0)),
   .mov .edx (.imm 1), .alu .sbb .edx (.imm 0)] ++
  (List.replicate 6 [.alu .add .ecx (.reg .ecx), .alu .adc .edx (.reg .edx)]).flatten

/-- With the state pointer in `eax`: the nonce, the number of bytes left and
the constants into the state. -/
def nonceStores : List Instr :=
  [.movdquStore (at_ .eax 48) .xmm0, .store (at_ .eax 128) .ecx, .store (at_ .eax 132) .edx,
   .mov .ecx (.imm 0x61707865), .store (at_ .eax 0) .ecx, .mov .ecx (.imm 0x3320646e), .store (at_ .eax 4) .ecx,
   .mov .ecx (.imm 0x79622d32), .store (at_ .eax 8) .ecx, .mov .ecx (.imm 0x6b206574), .store (at_ .eax 12) .ecx]

def setNonce : Prog isa :=
  .block ([.mov .eax (.mem (at_ .esp 4)), .mov .edx (.mem (at_ .esp 8))] ++ nonceLoads ++ nonceStores)

def init : Prog isa :=
  .block ([.mov .eax (.mem (at_ .esp 4)), .mov .ecx (.mem (at_ .esp 8)), .movdquLoad .xmm1 (at_ .ecx 0),
    .movdquLoad .xmm2 (at_ .ecx 16), .mov .edx (.mem (at_ .esp 12))] ++ nonceLoads ++
    [.movdquStore (at_ .eax 16) .xmm1, .movdquStore (at_ .eax 32) .xmm2] ++ nonceStores)

/-! ## `apply` -/

/-- With the state in `eax`: `edx:ecx` = the bytes left less `len`, and the
borrow whether fewer than `len` are left. -/
def check : List Instr :=
  [.mov .ecx (.mem (at_ .eax 128)), .mov .edx (.mem (at_ .eax 132)), .alu .sub .ecx (.mem (at_ .esp 12)),
   .alu .sbb .edx (.imm 0)]

/-- Saves our caller's registers and the bytes left after `apply`, loads the
arguments where they are kept, and compares the bytes left in the buffered
block (`eax`) with `len` (`ecx`). -/
def start : List Instr :=
  [.store (at_ .eax 576) .ebx, .store (at_ .eax 580) .esi, .store (at_ .eax 584) .edi,
   .store (at_ .eax 588) .ebp, .store (at_ .eax 600) .ecx, .store (at_ .eax 604) .edx,
   .mov .ebx (.reg .eax), .mov .esi (.mem (at_ .esp 8)), .mov .ebp (.mem (at_ .esp 12)),
   .mov .eax (.mem (at_ .ebx 128)), .alu .and .eax (.imm 63), .mov .ecx (.reg .ebp),
   .alu .cmp .eax (.reg .ebp)]

/-- XORs the `ecx` bytes at `edx` into the data (`esi`), advancing both. -/
def xorBytes : Prog isa :=
  .seq (.block [.alu .test .ecx (.reg .ecx)]) (.ite .e (.block []) xorLoop)

/-- Everything up to the whole blocks: the bytes left in the buffered block,
`ecx = min(eax, len)` of them, from `ebx + 128 - eax`, counted off `ebp`;
then `ecx` = the bytes of the whole blocks that follow (`ebp` rounded down
to a multiple of 64). -/
def part1 : Prog isa :=
  .seq (.block start)
  (.seq (.ite .b (.block [.mov .ecx (.reg .eax)]) (.block []))
  (.seq (.block (ptr .edx .ebx 128 ++ [.alu .sub .edx (.reg .eax), .alu .sub .ebp (.reg .ecx)]))
  (.seq xorBytes
    (.block [.mov .ecx (.reg .ebp), .alu .and .ecx (.imm 0xffffffc0)]))))

/-- The whole blocks: the state copied and the counter advanced, and the
arguments of `vg_chacha20_xor`; their length is kept in `edi`. -/
def blocksArgs : List Instr :=
  [.movdquLoad .xmm0 (at_ .ebx 0), .movdquLoad .xmm1 (at_ .ebx 16), .movdquLoad .xmm2 (at_ .ebx 32),
   .movdquLoad .xmm3 (at_ .ebx 48), .movdquStore (at_ .ebx 192) .xmm0, .movdquStore (at_ .ebx 208) .xmm1,
   .movdquStore (at_ .ebx 224) .xmm2, .movdquStore (at_ .ebx 240) .xmm3,
   .mov .eax (.reg .ecx), .shift .shr .eax 6, .alu .add .eax (.mem (at_ .ebx 48)), .store (at_ .ebx 48) .eax,
   .mov .edi (.reg .ecx)] ++ ptr .eax .ebx 256 ++ ptr .edx .ebx 192

/-- `vg_chacha20_xor(state + 192, data, ecx, state + 256)`. -/
def callXor : Prog isa := .frame (.push [.eax, .ecx, .esi, .edx]) (.call "vg_chacha20_xor" Xor.xor) (.pop .eax 4)

def part2 : Prog isa :=
  .ite .e (.block [])
    (.seq (.block blocksArgs) (.seq callXor (.block [.alu .add .esi (.reg .edi), .alu .sub .ebp (.reg .edi)])))

/-- `vg_chacha20_block(state, state + 64)`. -/
def callBlock : Prog isa := .frame (.push [.eax, .ebx]) (.call "vg_chacha20_block" block) (.pop .eax 2)

/-- After the block function: the counter advanced, and `ebp` bytes of the
block XORed. -/
def tailXor : Prog isa :=
  .seq (.block ([.mov .eax (.mem (at_ .ebx 48)), .alu .add .eax (.imm 1), .store (at_ .ebx 48) .eax] ++
    ptr .edx .ebx 64 ++ [.mov .ecx (.reg .ebp)]))
    xorBytes

/-- The last bytes, if any: the next block into the buffer, the counter
advanced, and `ebp` bytes of the block XORed. -/
def part3 : Prog isa :=
  .seq (.block [.alu .test .ebp (.reg .ebp)])
  (.ite .e (.block []) (.seq (.block (ptr .eax .ebx 64)) (.seq callBlock tailXor)))

/-- The bytes left stored, our caller's registers restored, and 1 returned. -/
def finish : List Instr :=
  [.mov .eax (.mem (at_ .ebx 600)), .store (at_ .ebx 128) .eax, .mov .eax (.mem (at_ .ebx 604)),
   .store (at_ .ebx 132) .eax, .mov .esi (.mem (at_ .ebx 580)), .mov .edi (.mem (at_ .ebx 584)),
   .mov .ebp (.mem (at_ .ebx 588)), .mov .ebx (.mem (at_ .ebx 576)), .mov .eax (.imm 1)]

def apply : Prog isa :=
  .seq (.block [.mov .eax (.mem (at_ .esp 4))]) (.seq (.block check)
  (.ite .b (.block [.mov .eax (.imm 0)])
    (.seq part1 (.seq part2 (.seq part3 (.block finish))))))

end VG.Impl.ChaCha20.X86.Stream
