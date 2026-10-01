import VerifiedGarbage.Impl.Aes.AArch64.Callee

/-!
# AES-CMAC: AArch64 implementation

`vg_cmac_aes_subkeys(schedule = x0, rounds = x1, subkeys = x2, scratch = x3)`,
`vg_cmac_aes_update(schedule = x0, rounds = x1, state = x2, data = x3, n = x4, scratch = x5)`
and `vg_cmac_aes_finalize(key = x0, rounds = x1, state = x2, last = x3, last_len = x4, scratch = x5)`
(see `VG.Spec.Cmac.aesSubkeysContract` and the others), composed of calls of
the verified `vg_aes_ctr32`, one block at a time: with a counter block `X`
and a zero data block, it leaves `CIPH_K(X)` in the data block. They are
generic over the implementation of `vg_aes_ctr32` they call (`Ctr32`): each
is emitted once for each implementation (e.g. `vg_cmac_aes_update` calls
`vg_aes_ctr32`, and `vg_cmac_aes_update_aes` calls `vg_aes_ctr32_aes`).

The scratch buffer (2176 bytes): `[0, 2048)` is the working space of
`vg_aes_ctr32`, `[2048, 2064)` the counter block, and `[2064, 2120)` our
caller's callee-saved registers and our return address `x30`. A call (`bl`)
stores nothing in memory, so no stack is used.

* `subkeys` computes `L = CIPH_K(0)` into the first block of `subkeys`, and
  doubles it there (`K1`) and into the second block (`K2`): the block as a
  big-endian 128-bit integer in `x9:x10`, shifted left by one bit, and
  XORed with `0x87` masked by the bit shifted out. `x19` holds `subkeys`
  and `x20` the scratch buffer across the call.
* `update` keeps its arguments in `x19` (schedule), `x20` (rounds), `x21`
  (state), `x22` (data), `x23` (blocks left) and `x24` (scratch) across the
  calls; each block, the counter block is `C ⊕ Mᵢ` and the state, zeroed,
  receives `CIPH_K(C ⊕ Mᵢ)`.
* `finalize` forms `Mₙ` in the counter block: `Mₙ* ⊕ K1` for a complete
  block, else `Mₙ*` copied a byte at a time onto zeros, `0x80` after it, and
  XORed with `K2`. It XORs in the chaining value and calls `vg_aes_ctr32`
  last, keeping only the scratch buffer (in `x19`) across the call.

The model has no flags or register-offset addressing: the branches are
`cbz`/`cbnz`, on `n`, on `last_len - 16` and on `last_len`, and the bytes are
copied through advancing pointers. Only the pointers, `rounds`, `n` and
`last_len` can affect timing: the doubling is masked.
-/

namespace VG.Impl.CmacAes.AArch64

open VG.AArch64
open VG.Impl.Aes.AArch64 (Ctr32)

/-- `mov d, n`. -/
def mov (d n : Reg) : Instr := .addImm .x d n 0

/-- The offset of the counter block in the scratch buffer. -/
def cOff : Nat := 2048

/-- The arguments of `vg_aes_ctr32` for one block, other than the schedule
and the rounds: the counter block at `scr + cOff`, the data block at `out`,
`n = 1`, and the working space at `scr`. -/
def ctrArgs (scr out : Reg) : List Instr :=
  [.addImm .x .x2 scr cOff, mov .x3 out, .movz .x .x4 1 0, mov .x5 scr]

/-! ## `vg_cmac_aes_subkeys` -/

/-- Saves `x19`, `x20` and `x30`, keeps `subkeys` in `x19` and the scratch
buffer in `x20`, zeroes the counter block and the first block of `subkeys`,
and sets up the arguments of `vg_aes_ctr32`. -/
def subkeysPre : List Instr :=
  [.str .x .x19 .x3 2064, .str .x .x20 .x3 2072, .str .x .x30 .x3 2080, mov .x19 .x2, mov .x20 .x3,
   .movz .x .x9 0 0, .str .x .x9 .x3 cOff, .str .x .x9 .x3 (cOff + 8), .str .x .x9 .x2 0,
   .str .x .x9 .x2 8] ++
  ctrArgs .x20 .x19

/-- The block at `x19 + src`, doubled (`VG.Spec.Cmac.dbl 16`), to `x19 + dst`. -/
def dbl (src dst : Nat) : List Instr :=
  [.ldr .x .x9 .x19 src, .ldr .x .x10 .x19 (src + 8), .rev .x9 .x9, .rev .x10 .x10,
   .lsr .x .x11 .x9 63, .movz .x .x12 0 0, .sub .x .x11 .x12 .x11, .movz .x .x12 0x87 0,
   .logic .and .x .x11 .x11 .x12,
   .lsr .x .x12 .x10 63, .lsl .x .x9 .x9 1, .logic .orr .x .x9 .x9 .x12,
   .lsl .x .x10 .x10 1, .logic .eor .x .x10 .x10 .x11,
   .rev .x9 .x9, .rev .x10 .x10, .str .x .x9 .x19 dst, .str .x .x10 .x19 (dst + 8)]

/-- `K1` over `L`, `K2` after it, and the saved registers restored. -/
def subkeysPost : List Instr :=
  dbl 0 0 ++ dbl 0 16 ++ [.ldr .x .x30 .x20 2080, .ldr .x .x19 .x20 2064, .ldr .x .x20 .x20 2072]

def subkeys (c : Ctr32) : Prog isa :=
  .seq (.block subkeysPre) (.seq (.call c.name c.code) (.block subkeysPost))

/-! ## `vg_cmac_aes_update` -/

/-- The registers saved in the scratch buffer, and where (`x24`, the base of
the restore, last). -/
def saved : List (Reg × Nat) :=
  [(.x19, 2064), (.x20, 2072), (.x21, 2080), (.x22, 2088), (.x23, 2096), (.x30, 2104), (.x24, 2112)]

def save : List Instr := saved.map fun (r, d) => .str .x r .x5 d

/-- Restores the registers, with `x24` (restored last) the scratch buffer. -/
def restore : List Instr := saved.map fun (r, d) => .ldr .x r .x24 d

/-- The arguments to their registers. -/
def setup : List Instr :=
  [mov .x19 .x0, mov .x20 .x1, mov .x21 .x2, mov .x22 .x3, mov .x23 .x4, mov .x24 .x5]

/-- The counter block `C ⊕ Mᵢ` (the state at `x21`, the block at `x22`), and
the state zeroed. -/
def chainIn : List Instr :=
  [.ldr .x .x9 .x21 0, .ldr .x .x10 .x22 0, .logic .eor .x .x9 .x9 .x10, .str .x .x9 .x24 cOff,
   .ldr .x .x9 .x21 8, .ldr .x .x10 .x22 8, .logic .eor .x .x9 .x9 .x10, .str .x .x9 .x24 (cOff + 8),
   .movz .x .x9 0 0, .str .x .x9 .x21 0, .str .x .x9 .x21 8]

/-- The arguments of `vg_aes_ctr32` for the block. -/
def updArgs : List Instr := [mov .x0 .x19, mov .x1 .x20] ++ ctrArgs .x24 .x21

/-- On to the next block. -/
def advance : List Instr := [.addImm .x .x22 .x22 16, .subImm .x .x23 .x23 1]

/-- One block. -/
def body (c : Ctr32) : Prog isa :=
  .seq (.block (chainIn ++ updArgs)) (.seq (.call c.name c.code) (.block advance))

def update (c : Ctr32) : Prog isa :=
  .seq (.block (save ++ setup))
    (.seq (.ite (.zero .x .x23) (.block []) (.loop (body c) (.nonzero .x .x23))) (.block restore))

/-! ## `vg_cmac_aes_finalize` -/

/-- `Mₙ = Mₙ* ⊕ K1` (`K1` at `x0 + 240`), for a complete last block. -/
def full : List Instr :=
  [.ldr .x .x9 .x3 0, .ldr .x .x10 .x0 240, .logic .eor .x .x9 .x9 .x10, .str .x .x9 .x5 cOff,
   .ldr .x .x9 .x3 8, .ldr .x .x10 .x0 248, .logic .eor .x .x9 .x9 .x10, .str .x .x9 .x5 (cOff + 8)]

/-- The counter block zeroed, with `x6` pointing at it, `x7` at the last
bytes and `x8` counting them. -/
def zero : List Instr :=
  [.movz .x .x9 0 0, .str .x .x9 .x5 cOff, .str .x .x9 .x5 (cOff + 8), .addImm .x .x6 .x5 cOff,
   mov .x7 .x3, mov .x8 .x4]

/-- The `x8` (nonzero) bytes at `x7` copied to `x6`, advancing both. -/
def copy : Prog isa :=
  .loop (.block [.ldrb .x9 .x7 0, .strb .x9 .x6 0, .addImm .x .x7 .x7 1, .addImm .x .x6 .x6 1,
    .subImm .x .x8 .x8 1]) (.nonzero .x .x8)

/-- `0x80` after the bytes (at `x6`), and the block XORed with `K2` (at
`x0 + 256`). -/
def padK2 : List Instr :=
  [.movz .x .x9 0x80 0, .strb .x9 .x6 0,
   .ldr .x .x9 .x5 cOff, .ldr .x .x10 .x0 256, .logic .eor .x .x9 .x9 .x10, .str .x .x9 .x5 cOff,
   .ldr .x .x9 .x5 (cOff + 8), .ldr .x .x10 .x0 264, .logic .eor .x .x9 .x9 .x10,
   .str .x .x9 .x5 (cOff + 8)]

/-- `Mₙ = K2 ⊕ (Mₙ* ‖ 10ʲ)`, for a partial last block (`last_len < 16`). -/
def partialBlock : Prog isa :=
  .seq (.block zero) (.seq (.ite (.zero .x .x4) (.block []) copy) (.block padK2))

/-- The counter block `C ⊕ Mₙ` (the state at `x2`), the state zeroed, `x19`
and `x30` saved and the scratch buffer kept in `x19`, and the arguments of
`vg_aes_ctr32` but the schedule (`x0`), the rounds (`x1`) and the working
space (`x5`), which are ours. -/
def finArgs : List Instr :=
  [.ldr .x .x9 .x5 cOff, .ldr .x .x10 .x2 0, .logic .eor .x .x9 .x9 .x10, .str .x .x9 .x5 cOff,
   .ldr .x .x9 .x5 (cOff + 8), .ldr .x .x10 .x2 8, .logic .eor .x .x9 .x9 .x10,
   .str .x .x9 .x5 (cOff + 8),
   .movz .x .x9 0 0, .str .x .x9 .x2 0, .str .x .x9 .x2 8,
   .str .x .x19 .x5 2064, .str .x .x30 .x5 2072, mov .x19 .x5,
   mov .x3 .x2, .addImm .x .x2 .x5 cOff, .movz .x .x4 1 0]

/-- Everything before the call. -/
def finPre : Prog isa :=
  .seq (.block [.subImm .x .x9 .x4 16])
    (.seq (.ite (.zero .x .x9) (.block full) partialBlock) (.block finArgs))

def finalize (c : Ctr32) : Prog isa :=
  .seq finPre (.seq (.call c.name c.code) (.block [.ldr .x .x30 .x19 2072, .ldr .x .x19 .x19 2064]))

end VG.Impl.CmacAes.AArch64
