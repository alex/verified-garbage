import VerifiedGarbage.Impl.CmacAes.X86
import VerifiedGarbage.Impl.Aes.X86.ExpandKey

/-!
# Streaming AES-CMAC: x86 (32-bit) implementation

`vg_cmac_aes_init(state, key, key_len, scratch)`,
`vg_cmac_aes_absorb(state, rounds, count, data, len, scratch)` and
`vg_cmac_aes_finish(state, rounds, count, out, scratch)` (see
`VG.Spec.Cmac.aesInitContract` and the others), every argument on the stack
(cdecl; `count` takes two slots, its low word first), composed of calls of
the verified `vg_aes_expand_key`, `vg_cmac_aes_subkeys`, `vg_cmac_aes_update`
and `vg_cmac_aes_finalize`.

The state (`VG.Spec.Cmac.Repr`) is the key schedule (bytes 0–239), the
subkeys (240–271), the chaining value (272–287) and the bytes held back
(288–303), so bytes 0–271 are `vg_cmac_aes_finalize`'s `key`. The scratch
buffer (2304 bytes): `[0, 2176)` is the working space of the functions
called, and `[2176, 2192)` our caller's `ebx`, `esi`, `edi` and `ebp`.

Each call pushes the callee's arguments (from `eax`, `ecx`, `edx`, `ebx`,
then `esi` and `edi` for six), last to first, in a frame of its own, popped
(into `eax`) when it returns. Everything but one number is reloaded from our
own stack arguments after a call, so all seven registers can hold arguments.

* `init` expands the key into the state, derives the subkeys after it and
  zeroes the chaining value.
* `absorb`: with `h` bytes held back (`count` modulo 16, but 16 for a
  multiple of 16 and 0 for the empty message), it copies
  `f = min(len, 16 - h)` bytes after them. If data is left (the block held
  back is whole and not the last), the first call chains that block, the
  second the whole blocks of what is left but its last 1 to 16 bytes, which
  the last copy copies to the start of the bytes held back. With no data
  left, the two calls chain no blocks and the last copy copies nothing, so
  the code has no branch around a call. Across the calls `ebp` holds the
  number of bytes of data consumed (`f`, then `f + 16 nb`).
* `finish` copies the chaining value to `out` and calls
  `vg_cmac_aes_finalize` with the state as its key, `out` as its state and
  the `h` bytes held back as the last bytes.

Only the pointers, the key length, `count` and `len` can affect timing: the
branches are on them, and so are the number of bytes copied and of blocks
chained.
-/

namespace VG.Impl.CmacAes.Stream.X86

open VG.X86
open VG.Impl.CmacAes.X86 (at_ argOp zero4)

/-- Our caller's callee-saved registers, and where they are saved in the
scratch buffer. -/
def saved : List (Reg × Nat) := [(.ebx, 2176), (.esi, 2180), (.edi, 2184), (.ebp, 2188)]

/-- Save them, with the scratch buffer in `eax`. -/
def save : List Instr := saved.map fun (r, d) => .store (at_ .eax d) r

/-- Restore them, with the scratch buffer (the stack argument `i`) loaded into `eax`. -/
def restore (i : Nat) : List Instr := .mov .eax (argOp i) :: saved.map fun (r, d) => .mov r (.mem (at_ .eax d))

/-- A call of a function of four arguments, `eax`, `ecx`, `edx` and `ebx`. -/
def call4 (name : String) (code : Prog isa) : Prog isa :=
  .frame (.push [.ebx, .edx, .ecx, .eax]) (.call name code) (.pop .eax 4)

/-- A call of a function of six arguments, `eax`, `ecx`, `edx`, `ebx`, `esi` and `edi`. -/
def call6 (name : String) (code : Prog isa) : Prog isa :=
  .frame (.push [.edi, .esi, .ebx, .edx, .ecx, .eax]) (.call name code) (.pop .eax 6)

/-- The `ecx` bytes at `esi` copied to `edi` (none if `ecx` is 0). -/
def copy : Prog isa := .seq (.block [.alu .test .ecx (.reg .ecx)]) (.ite .e (.block []) Impl.CmacAes.X86.copy)

/-- `count`'s low word (the stack argument 2) in `r`; ZF set if `count` is 0. -/
def count0 (r : Reg) : List Instr := [.mov r (argOp 2), .mov .ecx (argOp 3), .alu .or .ecx (.reg r)]

/-- The number of bytes held back for `count`, in `r`, from `count0 r`. -/
def held (r : Reg) : Prog isa :=
  .ite .e (.block []) (.block [.alu .sub r (.imm 1), .alu .and r (.imm 15), .alu .add r (.imm 1)])

/-- The number of bytes held back for `count`, in `r` (`ecx` clobbered). -/
def countHeld (r : Reg) : Prog isa := .seq (.block (count0 r)) (held r)

/-! ## `vg_cmac_aes_init` -/

/-- Saves the registers and sets up the arguments of
`vg_aes_expand_key(key, key_len, schedule = state, scratch)`. -/
def initPre : List Instr :=
  [.mov .eax (argOp 3)] ++ save ++ [.mov .eax (argOp 1), .mov .ecx (argOp 2), .mov .edx (argOp 0), .mov .ebx (argOp 3)]

/-- The arguments of `vg_cmac_aes_subkeys(schedule = state, rounds, subkeys = state + 240, scratch)`,
with the rounds `key_len / 4 + 6`. -/
def initMid : List Instr :=
  [.mov .eax (argOp 0), .mov .ecx (argOp 2), .shift .shr .ecx 2, .alu .add .ecx (.imm 6), .mov .edx (.reg .eax),
   .alu .add .edx (.imm 240), .mov .ebx (argOp 3)]

/-- The chaining value zeroed, and the registers restored. -/
def initPost : List Instr := [.mov .edx (argOp 0)] ++ zero4 .edx 272 ++ restore 3

def init : Prog isa :=
  .seq (.block initPre)
    (.seq (call4 "vg_aes_expand_key" Impl.Aes.X86.expandKey)
      (.seq (.block initMid) (.seq (call4 "vg_cmac_aes_subkeys" Impl.CmacAes.X86.subkeys) (.block initPost))))

/-! ## `vg_cmac_aes_absorb` -/

/-- Saves the registers. -/
def absSave : List Instr := [.mov .eax (argOp 6)] ++ save

/-- `f = min(len, 16 - h)` (`h` in `eax`) in `ecx` and `ebp`, the data in
`esi` and the destination `state + 288 + h` in `edi`. -/
def fill : Prog isa :=
  .seq (.block [.mov .ecx (.imm 16), .alu .sub .ecx (.reg .eax), .mov .edx (argOp 5), .alu .cmp .edx (.reg .ecx)])
    (.seq (.ite .b (.block [.mov .ecx (.reg .edx)]) (.block []))
      (.block [.mov .ebp (.reg .ecx), .mov .esi (argOp 4), .mov .edi (argOp 0), .alu .add .edi (.imm 288),
        .alu .add .edi (.reg .eax)]))

/-- The arguments of `vg_cmac_aes_update(schedule, rounds, state, data, n, scratch)` for
the block held back: `n = 1` if data is left, else 0. -/
def chain1 : Prog isa :=
  .seq (.block [.mov .esi (.imm 0), .mov .edx (argOp 5), .alu .sub .edx (.reg .ebp)])
    (.seq (.ite .e (.block []) (.block [.mov .esi (.imm 1)]))
      (.block [.mov .eax (argOp 0), .mov .ecx (argOp 1), .mov .edx (.reg .eax), .alu .add .edx (.imm 272),
        .mov .ebx (.reg .eax), .alu .add .ebx (.imm 288), .mov .edi (argOp 6)]))

/-- `16 nb` in `ecx` for the `nb` whole blocks of the data left but its last
1 to 16 bytes (none if no data is left), `ebp` advanced past them, and the
arguments of `vg_cmac_aes_update` for them: the data left, at `data + f`
(with no data left, the bytes held back, which the call reads none of, as
`data + f` may be the end of the address space). -/
def chain2 : Prog isa :=
  .seq (.block [.mov .ecx (.imm 0), .mov .ebx (argOp 0), .alu .add .ebx (.imm 288), .mov .edx (argOp 5),
      .alu .sub .edx (.reg .ebp)])
    (.seq (.ite .e (.block [])
        (.block [.mov .ecx (.reg .edx), .alu .sub .ecx (.imm 1), .mov .eax (.reg .ecx), .alu .and .eax (.imm 15),
          .alu .sub .ecx (.reg .eax), .mov .ebx (argOp 4), .alu .add .ebx (.reg .ebp)]))
      (.block [.mov .esi (.reg .ecx), .shift .shr .esi 4, .alu .add .ebp (.reg .ecx), .mov .eax (argOp 0),
        .mov .ecx (argOp 1), .mov .edx (.reg .eax), .alu .add .edx (.imm 272), .mov .edi (argOp 6)]))

/-- The arguments of the copy of the rest to the start of the bytes held back. -/
def rest : List Instr :=
  [.mov .esi (argOp 4), .alu .add .esi (.reg .ebp), .mov .edi (argOp 0), .alu .add .edi (.imm 288),
   .mov .ecx (argOp 5), .alu .sub .ecx (.reg .ebp)]

/-- Everything before the first call. -/
def absorbPre : Prog isa := .seq (.block absSave) (.seq (countHeld .eax) (.seq fill (.seq copy chain1)))

/-- Everything after the second call. -/
def absorbPost : Prog isa := .seq (.block rest) (.seq copy (.block (restore 6)))

def absorb : Prog isa :=
  .seq absorbPre
    (.seq (call6 "vg_cmac_aes_update" Impl.CmacAes.X86.update)
      (.seq chain2 (.seq (call6 "vg_cmac_aes_update" Impl.CmacAes.X86.update) absorbPost)))

/-! ## `vg_cmac_aes_finish` -/

/-- Saves the registers, and sets up the copy of the chaining value to `out`. -/
def finSave : List Instr :=
  [.mov .eax (argOp 5)] ++ save ++ [.mov .esi (argOp 0), .alu .add .esi (.imm 272), .mov .edi (argOp 4),
    .mov .ecx (.imm 16)]

/-- The arguments of
`vg_cmac_aes_finalize(key = state, rounds, state = out, last = state + 288, last_len, scratch)`
but `last_len` (in `esi`). -/
def finArgs : List Instr :=
  [.mov .eax (argOp 0), .mov .ecx (argOp 1), .mov .edx (argOp 4), .mov .ebx (.reg .eax), .alu .add .ebx (.imm 288),
   .mov .edi (argOp 5)]

/-- Everything before the call. -/
def finPre : Prog isa :=
  .seq (.block finSave) (.seq copy (.seq (countHeld .esi) (.block finArgs)))

def finish : Prog isa :=
  .seq finPre (.seq (call6 "vg_cmac_aes_finalize" Impl.CmacAes.X86.finalize) (.block (restore 5)))

end VG.Impl.CmacAes.Stream.X86
