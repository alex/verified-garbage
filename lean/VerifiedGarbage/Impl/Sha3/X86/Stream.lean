import VerifiedGarbage.Impl.Sha3.X86

/-!
# The SHA-3 sponge: x86 (32-bit) implementation

The same structure as the x86-64 implementation. The streaming state is the
Keccak state (`[u64; 25]` at `state`), with the bytes of a partial block
XORed into it as they arrive (see `VG.Spec.Sha3.Repr`); the position in the
block is kept by the caller. Every argument is on the stack (cdecl).

* `absorb(state, rate, pos, data, len, scratch)` XORs the bytes of `data`
  into the state one at a time, from byte `pos`, permuting the state
  whenever a block is complete, and returns the position after them.
* `pad(state, rate, pos, suffix, scratch)` XORs the suffix into byte `pos`
  and `0x80` into byte `rate - 1`, and permutes the state.
* `squeeze(state, rate, pos, out, outlen, scratch)` copies the state to `out`
  one byte at a time from byte `pos`, permuting it whenever a block has been
  used up and more output is needed, and returns the position after them.

The permutation is called (`vg_keccak_f1600`, `Impl.Sha3.X86.permute`) with
the first 512 bytes of `scratch` as its scratch space. Each call pushes its
two arguments (`scratch`, then `state`) in a frame of its own, popped (into
`eax`) when it returns: with the return address the call stores, it uses the
12 bytes below `esp`. The permutation preserves `ebx`, `esi`, `edi` and
`ebp`, so `absorb` and `squeeze` keep their variables there across it
(`ebx` = `state`, `ebp` = `scratch`, `esi` = `data` or `out`, `edi` = the
bytes of it left), save their caller's values of those registers in
`scratch[512..528)`, and keep `state + pos` (the address of the next byte of
the state) and `rate` in `scratch[528..536)`: loaded into `ecx` and `edx`,
and stored back, around each byte stored. The constant-time analysis cannot
tell where a byte of the state or of `out` is, so it forgets that any memory
is public after such a store, and relearns it from the stores back; and it
cannot follow the arguments on the stack across a call. For the same
reasons `pad` keeps `scratch` in `esi` across its call (saving its caller's
`ebx` and `esi` in `scratch[512..520)`), and reads its arguments before its
stores. A byte of `data` is XORed with the (little-endian) word at `state +
pos`, whose low byte is that byte of the state (the word lies within the
state: `pos < rate ≤ 168`). Values the analysis must know to be public are
loaded from memory with `mov`. Every address and branch depends only on
`esp`, the pointers, `rate`, `pos` and the lengths.
-/

namespace VG.Impl.Sha3.X86.Stream

open VG.X86
open VG.Impl.Sha512.X86 (at_)
open VG.Impl.Sha3.X86 (permute)

/-- The callee-saved registers, and where they are saved in `scratch`. -/
def saved : List (Reg × Nat) := [(.ebx, 512), (.esi, 516), (.edi, 520), (.ebp, 524)]

/-- Save them, with `scratch` in `eax`. -/
def save : List Instr := saved.map fun (r, d) => .store (at_ .eax d) r

/-- Restore them, with `scratch` in `ecx`. -/
def restore : List Instr := saved.map fun (r, d) => .mov r (.mem (at_ .ecx d))

/-- A call of `vg_keccak_f1600(st, scr)`: its arguments pushed last to first. -/
def permuteCall (st scr : Reg) : Prog isa :=
  .frame (.push [scr, st]) (.call "vg_keccak_f1600" permute) (.pop .eax 2)

/-- Where `state + pos` (the address of the next byte of the state) and
`rate` are kept, in `scratch`. -/
def pOff : Nat := 528
def rOff : Nat := 532

/-- Save the registers; `ebp` = `scratch`, `ebx` = `state`, `esi` = `data`
or `out`, `edi` = its length; store `state + pos` and `rate` in `scratch`;
then test `edi`. -/
def setup : List Instr :=
  .mov .eax (.mem (at_ .esp 24)) :: save ++
    [.mov .ebp (.reg .eax), .mov .ebx (.mem (at_ .esp 4)), .mov .ecx (.mem (at_ .esp 12)),
      .alu .add .ecx (.reg .ebx), .store (at_ .ebp pOff) .ecx, .mov .ecx (.mem (at_ .esp 8)),
      .store (at_ .ebp rOff) .ecx, .mov .esi (.mem (at_ .esp 16)), .mov .edi (.mem (at_ .esp 20)),
      .alu .test .edi (.reg .edi)]

/-- Return the position, and restore the registers. -/
def epilogue : List Instr :=
  .mov .eax (.mem (at_ .ebp pOff)) :: .alu .sub .eax (.reg .ebx) :: .mov .ecx (.reg .ebp) :: restore

/-- `state + pos` into `ecx` and `rate` into `edx`. -/
def loadVars : List Instr := [.mov .ecx (.mem (at_ .ebp pOff)), .mov .edx (.mem (at_ .ebp rOff))]

/-- The next position, and `rate`, stored back. -/
def storeVars : List Instr :=
  [.alu .add .ecx (.imm 1), .store (at_ .ebp pOff) .ecx, .store (at_ .ebp rOff) .edx]

/-- Advance to the next byte of data or output. -/
def step : List Instr := [.alu .add .esi (.imm 1), .alu .sub .edi (.imm 1)]

/-- Set ZF if the position (`ecx - ebx`) is `rate` (`edx`). -/
def atEnd : List Instr := [.mov .eax (.reg .ecx), .alu .sub .eax (.reg .ebx), .alu .cmp .eax (.reg .edx)]

/-- If the block is used up, go back to its start and permute the state. -/
def next : Prog isa :=
  .ite .e (.seq (.block [.store (at_ .ebp pOff) .ebx]) (permuteCall .ebx .ebp)) (.block [])

/-! ## `absorb` -/

/-- XOR the byte of data at `esi` into the state at `ecx`. -/
def absorbByte : List Instr :=
  [.movzx8 .eax (at_ .esi 0), .alu .xor .eax (.mem (at_ .ecx 0)), .store8 (at_ .ecx 0) .al]

def absorbBody : Prog isa :=
  .seq (.block (loadVars ++ absorbByte ++ storeVars ++ step ++ atEnd))
    (.seq next (.block [.alu .test .edi (.reg .edi)]))

def absorb : Prog isa :=
  .seq (.block setup) (.seq (.ite .e (.block []) (.loop absorbBody .ne)) (.block epilogue))

/-! ## `pad` -/

/-- Save `ebx` and `esi` in `scratch`, which is then kept in `esi`; `ecx` =
`state`, `eax` = `rate`. XOR the suffix into byte `pos` of the state and
`0x80` into byte `rate - 1`, with `ebx` as a temporary. -/
def padBytes : List Instr :=
  [.mov .eax (.mem (at_ .esp 20)), .store (at_ .eax 512) .ebx, .store (at_ .eax 516) .esi,
    .mov .esi (.reg .eax), .mov .ecx (.mem (at_ .esp 4)), .mov .eax (.mem (at_ .esp 8)),
    .mov .edx (.mem (at_ .esp 12)), .alu .add .edx (.reg .ecx), .movzx8 .ebx (at_ .edx 0),
    .alu .xor .ebx (.mem (at_ .esp 16)), .store8 (at_ .edx 0) .bl,
    .mov .edx (.reg .ecx), .alu .add .edx (.reg .eax), .alu .sub .edx (.imm 1),
    .movzx8 .ebx (at_ .edx 0), .alu .xor .ebx (.imm 0x80), .store8 (at_ .edx 0) .bl]

def pad : Prog isa :=
  .seq (.block padBytes)
    (.seq (permuteCall .ecx .esi) (.block [.mov .ebx (.mem (at_ .esi 512)), .mov .esi (.mem (at_ .esi 516))]))

/-! ## `squeeze` -/

/-- Copy the byte of the state at `ecx` to `out` at `esi`. -/
def squeezeByte : List Instr := [.movzx8 .eax (at_ .ecx 0), .store8 (at_ .esi 0) .al]

def squeezeBody : Prog isa :=
  .seq (.block (loadVars ++ atEnd))
    (.seq next (.block (loadVars ++ squeezeByte ++ storeVars ++ step)))

def squeeze : Prog isa :=
  .seq (.block setup) (.seq (.ite .e (.block []) (.loop squeezeBody .ne)) (.block epilogue))

end VG.Impl.Sha3.X86.Stream
