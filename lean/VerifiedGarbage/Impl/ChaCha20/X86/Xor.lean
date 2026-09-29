import VerifiedGarbage.Impl.ChaCha20.X86

/-!
# ChaCha20 keystream XOR: x86 (32-bit) implementation

`vg_chacha20_xor(state, data, len, buf)`, cdecl: the arguments are at
`[esp + 4]`, `[esp + 8]`, `[esp + 12]` and `[esp + 16]`.

For each 64 bytes of data (the last piece may be shorter),
`vg_chacha20_block(state, buf)` is called, the first `n = min(64, remaining)`
bytes of its output (the first 64 bytes of `buf`) are XORed into the data a
byte at a time, and the block counter (word 12 of the state) is incremented
modulo 2³².

Across the calls, `ebx` holds `state`, `esi` the data not yet processed,
`edi` `buf` and `ebp` the number of bytes left: the block function preserves
them (it is cdecl). Our caller's values of those registers are saved in
`buf[256, 272)`, which is not passed to the block function. Each call pushes
its two arguments (`buf`, then `state`) in a frame of its own, popped (into
`eax`) when it returns: with the return address the call stores, it uses the
12 bytes below `esp`.

In the byte loop, `edx` points at the next byte of keystream and `ecx`
counts the bytes left; the data byte is XORed with the (little-endian) word
at `edx`, whose low byte is that keystream byte (the word lies within
`buf`). Afterwards `edx - edi` is the number of bytes done.

The branches are on the length only, and every address is `esp`, a pointer
or a pointer plus a count, so only the pointers and the length can affect
timing. On return `eax` holds `buf`.
-/

namespace VG.Impl.ChaCha20.X86.Xor

open VG.X86
open VG.Impl.ChaCha20.X86 (at_ block)

/-- Our caller's callee-saved registers, and where they are saved in `buf`. -/
def saved : List (Reg × Nat) := [(.ebx, 256), (.esi, 260), (.edi, 264), (.ebp, 268)]

/-- Save them, with `buf` in `eax`. -/
def save : List Instr := saved.map fun (r, d) => .store (at_ .eax d) r

/-- Restore them, with `buf` in `eax`. -/
def restore : List Instr := saved.map fun (r, d) => .mov r (.mem (at_ .eax d))

/-- With `buf` in `eax`: save our caller's registers, load the other
arguments, and test the length. -/
def prologue : List Instr :=
  save ++ [.mov .edi (.reg .eax), .mov .ebx (.mem (at_ .esp 4)), .mov .esi (.mem (at_ .esp 8)),
    .mov .ebp (.mem (at_ .esp 12)), .alu .test .ebp (.reg .ebp)]

/-- `vg_chacha20_block(state, buf)`: the keystream block into `buf`. -/
def callBlock : Prog isa :=
  .frame (.push [.edi, .ebx]) (.call "vg_chacha20_block" block) (.pop .eax 2)

/-- One byte: the data byte at `esi`, XORed with the keystream byte at `edx`. -/
def xorBody : List Instr :=
  [.movzx8 .eax (at_ .esi 0), .alu .xor .eax (.mem (at_ .edx 0)), .store8 (at_ .esi 0) .al,
   .alu .add .esi (.imm 1), .alu .add .edx (.imm 1), .alu .sub .ecx (.imm 1)]

/-- XORs the first `ecx` bytes of the keystream into the data. -/
def xorLoop : Prog isa := .loop (.block xorBody) .ne

/-- `ecx = min(64, ebp)`, and `edx` at the keystream. -/
def select : Prog isa :=
  .seq (.block [.mov .ecx (.reg .ebp), .alu .cmp .ebp (.imm 64)])
  (.seq (.ite .b (.block []) (.block [.mov .ecx (.imm 64)])) (.block [.mov .edx (.reg .edi)]))

/-- Increment the counter, and subtract the bytes done from those left. -/
def next : List Instr :=
  [.mov .eax (.mem (at_ .ebx 48)), .alu .add .eax (.imm 1), .store (at_ .ebx 48) .eax,
   .alu .sub .edx (.reg .edi), .alu .sub .ebp (.reg .edx)]

/-- One block of keystream, XORed into up to 64 bytes of data. -/
def body : Prog isa := .seq callBlock (.seq select (.seq xorLoop (.block next)))

def xor : Prog isa :=
  .seq (.block [.mov .eax (.mem (at_ .esp 16))])
  (.seq (.block prologue)
  (.seq (.ite .e (.block []) (.loop body .ne))
    (.block (.mov .eax (.reg .edi) :: restore))))

end VG.Impl.ChaCha20.X86.Xor
