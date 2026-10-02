import VerifiedGarbage.Impl.CmacAes.Arm
import VerifiedGarbage.Impl.Aes.Arm.ExpandKey

/-!
# Streaming AES-CMAC: 32-bit ARM implementation

`vg_cmac_aes_init(state = r0, key = r1, key_len = r2, scratch = r3)`,
`vg_cmac_aes_absorb(state = r0, rounds = r1, count = r2:r3, data = [sp], len = [sp, #4], scratch = [sp, #8])`
and `vg_cmac_aes_finish(state = r0, rounds = r1, count = r2:r3, out = [sp], scratch = [sp, #4])`
(see `VG.Spec.Cmac.aesInitContract` and the others), composed of calls of
the verified `vg_aes_expand_key`, `vg_cmac_aes_subkeys`, `vg_cmac_aes_update`
and `vg_cmac_aes_finalize`, as on x86-64 (`Impl/CmacAes/Stream/X86_64.lean`).

The state (`VG.Spec.Cmac.Repr`) is the key schedule (bytes 0–239), the
subkeys (240–271), the chaining value (272–287) and the bytes held back
(288–303), so bytes 0–271 are `vg_cmac_aes_finalize`'s `key`. The scratch
buffer (2304 bytes): `[0, 2176)` is the working space of the functions
called, and `[2176, 2208)` our caller's callee-saved registers and our
return address `lr`, which every call replaces.

`vg_cmac_aes_update` and `vg_cmac_aes_finalize` take their last two
arguments on the stack: a frame pushes them (`push {rA, rB}`) around each
call, and its pop loads `rA` back. Each uses 8 bytes of stack below that,
so `absorb` and `finish` use 16 bytes of stack, and `init` (whose call of
`vg_cmac_aes_subkeys` takes no stack arguments) 8.

* `init` expands the key into the state, derives the subkeys after it and
  zeroes the chaining value, keeping the state (`r4`), the scratch buffer
  (`r5`) and the rounds (`key_len / 4 + 6`, `r6`) across the calls.
* `absorb` keeps the state (`r4`), the rounds (`r5`), the data (`r6`,
  advancing, with `r7` bytes left), `16 nb` (`r8`) and the scratch buffer
  (`r10`) across the calls, and passes `n` in `r9`. With `h` bytes held back
  (`count` modulo 16, but 16 for a multiple of 16 and 0 for the empty
  message: `((count_lo - 1) & 15) + 1` if `count_lo | count_hi` is not 0),
  it copies `f = min(len, 16 - h)` bytes after them. If data is left (the
  block held back is whole and not the last), it chains that block, then
  the whole blocks of what is left but its last 1 to 16 bytes, which it
  copies to the start of the bytes held back. With no data left, the two
  calls chain no blocks (the second from the state, as the data may then
  end at the end of the address space) and the second copy copies nothing,
  so the code has no branch around a call.
* `finish` copies the chaining value to `out` and calls
  `vg_cmac_aes_finalize` with the state as its key, `out` as its state and
  the `h` bytes held back as the last bytes.

The model has no register-offset addressing: bytes are copied through
advancing pointers, counting down with `subs`, and `min(len, 16 - h)` is
computed with shifts tested by `cmp`. Only the pointers, the key length,
`count` and `len` can affect timing: the branches are on them, and so are
the number of bytes copied and of blocks chained.
-/

namespace VG.Impl.CmacAes.Stream.Arm

open VG.Arm
open VG.Impl.CmacAes.Arm (mov)

/-- Where our caller's callee-saved registers are kept in the scratch buffer. -/
def sOff : Nat := 2176

/-! ## `vg_cmac_aes_init` -/

/-- Saves `r4`–`r6` and `lr`, keeps the state in `r4`, the scratch buffer in
`r5` and the rounds (`key_len / 4 + 6`) in `r6`, and sets up the arguments
of `vg_aes_expand_key(key = r0, key_len = r1, schedule = r2, scratch = r3)`. -/
def initPre : List Instr :=
  [.str .r4 .r3 2176, .str .r5 .r3 2180, .str .r6 .r3 2184, .str .lr .r3 2188, mov .r4 .r0, mov .r5 .r3,
   .mov .r6 (.shifted .r2 .lsr 2), .dp .add .r6 .r6 (.imm 6), mov .r0 .r1, mov .r1 .r2, mov .r2 .r4]

/-- The arguments of `vg_cmac_aes_subkeys(schedule = r0, rounds = r1, subkeys = r2, scratch = r3)`. -/
def initMid : List Instr :=
  [mov .r0 .r4, mov .r1 .r6, .dp .add .r2 .r4 (.imm 240), mov .r3 .r5]

/-- The chaining value zeroed, and the registers restored (`r5` last). -/
def initPost : List Instr :=
  [.mov .r12 (.imm 0), .str .r12 .r4 272, .str .r12 .r4 276, .str .r12 .r4 280, .str .r12 .r4 284,
   .ldr .r4 .r5 2176, .ldr .r6 .r5 2184, .ldr .lr .r5 2188, .ldr .r5 .r5 2180]

def init : Prog isa :=
  .seq (.block initPre)
    (.seq (.call "vg_aes_expand_key" Impl.Aes.Arm.expandKey)
      (.seq (.block initMid) (.seq (.call "vg_cmac_aes_subkeys" Impl.CmacAes.Arm.subkeys)
        (.block initPost))))

/-! ## Copying bytes -/

/-- The loop's body: one byte from `[r6]` to `[r2]`, advancing both, with
`r1` bytes left. -/
def copyBody : List Instr :=
  [.ldrb .r12 .r6 0, .strb .r12 .r2 0, .dp .add .r6 .r6 (.imm 1), .dp .add .r2 .r2 (.imm 1),
   .subs .r1 .r1 (.imm 1)]

/-- The `r1` bytes at `r6` (none if `r1` is 0) copied to `r2`, advancing
both, and taken off the data left (`r7`). -/
def copy : Prog isa :=
  .seq (.block [.dp .sub .r7 .r7 (.reg .r1), .cmp .r1 (.imm 0)])
    (.ite .eq (.block []) (.loop (.block copyBody) .ne))

/-! ## `vg_cmac_aes_absorb` -/

/-- The registers saved in the scratch buffer, and where (`r10`, the base of
the restore, last). -/
def saved : List (Reg × Nat) :=
  [(.r4, 2176), (.r5, 2180), (.r6, 2184), (.r7, 2188), (.r8, 2192), (.r9, 2196), (.lr, 2204),
   (.r10, 2200)]

/-- Saves them, with the scratch buffer (the third stack argument) in `r12`,
and keeps the arguments in registers. -/
def save : List Instr :=
  .ldrSp .r12 8 :: saved.map (fun (r, d) => .str r .r12 d) ++
  [mov .r4 .r0, mov .r5 .r1, .ldrSp .r6 0, .ldrSp .r7 4, mov .r10 .r12]

/-- The number of bytes held back for `count` (`r2:r3`), in `r0`. -/
def held : Prog isa :=
  .seq (.block [.dp .sub .r0 .r2 (.imm 1), .dp .and .r0 .r0 (.imm 15), .dp .add .r0 .r0 (.imm 1),
      .dp .orr .r12 .r2 (.reg .r3), .cmp .r12 (.imm 0)])
    (.ite .eq (.block [.mov .r0 (.imm 0)]) (.block []))

/-- `f = min(len, 16 - h)` in `r1`: `16 - h`, or `len` if `len < 16` and
`len + h < 16`; and the destination `state + 288 + h` in `r2`. -/
def fill : Prog isa :=
  .seq (.block [.mov .r1 (.imm 16), .dp .sub .r1 .r1 (.reg .r0), .mov .r12 (.shifted .r7 .lsr 4),
      .cmp .r12 (.imm 0)])
    (.seq (.ite .eq
        (.seq (.block [.dp .add .r12 .r7 (.reg .r0), .mov .r12 (.shifted .r12 .lsr 4), .cmp .r12 (.imm 0)])
          (.ite .eq (.block [mov .r1 .r7]) (.block [])))
        (.block []))
      (.block [.dp .add .r2 .r4 (.reg .r0), .dp .add .r2 .r2 (.imm 288)]))

/-- One block to chain (`r9`) if data is left, else none; and the other
arguments of `vg_cmac_aes_update(schedule = r0, rounds = r1, state = r2,
data = r3, n = [sp], scratch = [sp, #4])` for the block held back. -/
def chain1 : Prog isa :=
  .seq (.block [.mov .r9 (.imm 0), .cmp .r7 (.imm 0)])
    (.seq (.ite .eq (.block []) (.block [.mov .r9 (.imm 1)]))
      (.block [mov .r0 .r4, mov .r1 .r5, .dp .add .r2 .r4 (.imm 272), .dp .add .r3 .r4 (.imm 288)]))

/-- The call of `vg_cmac_aes_update`, with `n` in `r9` and the scratch
buffer in `r10` pushed as its stack arguments, and `r9` popped. -/
def updCall : Prog isa :=
  .frame (.push [.r9, .r10]) (.call "vg_cmac_aes_update" Impl.CmacAes.Arm.update) (.pop .r9 8)

/-- `nb` in `r9` and `16 nb` in `r8` for the `nb` whole blocks of the data
left but its last 1 to 16 bytes (none if no data is left, then at the
state), and the arguments of `vg_cmac_aes_update` for them. -/
def chain2 : Prog isa :=
  .seq (.block [.cmp .r7 (.imm 0)])
    (.seq (.ite .eq (.block [.mov .r9 (.imm 0), .mov .r8 (.imm 0), mov .r3 .r4])
        (.block [.dp .sub .r9 .r7 (.imm 1), .mov .r9 (.shifted .r9 .lsr 4), .mov .r8 (.shifted .r9 .lsl 4),
          mov .r3 .r6]))
      (.block [mov .r0 .r4, mov .r1 .r5, .dp .add .r2 .r4 (.imm 272)]))

/-- The data advanced past the blocks chained, and the arguments of the
copy of the rest to the start of the bytes held back. -/
def rest : List Instr :=
  [.dp .add .r6 .r6 (.reg .r8), .dp .sub .r7 .r7 (.reg .r8), mov .r1 .r7, .dp .add .r2 .r4 (.imm 288)]

/-- Restores the registers, with `r10` (restored last) the scratch buffer. -/
def restore : List Instr := saved.map fun (r, d) => .ldr r .r10 d

/-- Everything before the first call. -/
def absorbPre : Prog isa := .seq (.block save) (.seq held (.seq fill (.seq copy chain1)))

/-- Everything after the second call. -/
def absorbPost : Prog isa := .seq (.block rest) (.seq copy (.block restore))

def absorb : Prog isa :=
  .seq absorbPre (.seq updCall (.seq chain2 (.seq updCall absorbPost)))

/-! ## `vg_cmac_aes_finish` -/

/-- Saves `r4`, `r5` and `lr`, keeps the scratch buffer in `r5`, copies the
chaining value to `out` (in `r12`), and computes the number of bytes held
back for `count` (`r2:r3`) in `r4` but for the empty message; Z is set if
`count` is 0. -/
def finishPre : List Instr :=
  [.ldrSp .r12 4, .str .r4 .r12 2176, .str .r5 .r12 2180, .str .lr .r12 2184, mov .r5 .r12, .ldrSp .r12 0,
   .ldr .lr .r0 272, .str .lr .r12 0, .ldr .lr .r0 276, .str .lr .r12 4, .ldr .lr .r0 280, .str .lr .r12 8,
   .ldr .lr .r0 284, .str .lr .r12 12,
   .dp .sub .r4 .r2 (.imm 1), .dp .and .r4 .r4 (.imm 15), .dp .add .r4 .r4 (.imm 1),
   .dp .orr .r2 .r2 (.reg .r3), .cmp .r2 (.imm 0)]

/-- `last_len`: none for the empty message. -/
def lastLen : Prog isa := .ite .eq (.block [.mov .r4 (.imm 0)]) (.block [])

/-- The arguments of `vg_cmac_aes_finalize(key = r0, rounds = r1, state = r2,
last = r3, last_len = [sp], scratch = [sp, #4])` but the stack ones: the
state as the key, `out` as the state, and the bytes held back. -/
def finArgs : List Instr := [mov .r2 .r12, .dp .add .r3 .r0 (.imm 288)]

/-- The call of `vg_cmac_aes_finalize`, with `last_len` in `r4` and the
scratch buffer in `r5` pushed as its stack arguments, and `r4` popped. -/
def finCall : Prog isa :=
  .frame (.push [.r4, .r5]) (.call "vg_cmac_aes_finalize" Impl.CmacAes.Arm.finalize) (.pop .r4 8)

/-- Restores the registers (`r5` last). -/
def finishPost : List Instr := [.ldr .r4 .r5 2176, .ldr .lr .r5 2184, .ldr .r5 .r5 2180]

/-- Everything before the call. -/
def finPre : Prog isa := .seq (.block finishPre) (.seq lastLen (.block finArgs))

def finish : Prog isa := .seq finPre (.seq finCall (.block finishPost))

end VG.Impl.CmacAes.Stream.Arm
