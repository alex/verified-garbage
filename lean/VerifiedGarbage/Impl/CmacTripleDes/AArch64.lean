import VerifiedGarbage.Impl.CmacTripleDes.AArch64.Round

/-!
# TDEA-CMAC (3DES-CMAC): AArch64 implementation

`vg_cmac_triple_des_init(key = x0, key_len = x1, out = x2, scratch = x3)`,
`vg_cmac_triple_des_update(schedule = x0, state = x1, data = x2, n = x3, scratch = x4)`
and `vg_cmac_triple_des_finalize(key = x0, state = x1, last = x2, last_len = x3, scratch = x4)`
(see `VG.Spec.Cmac.tdesInitContract` and the others), as on x86-64
(`Impl/CmacTripleDes/X86_64.lean`). Each encrypts blocks with `block`
(`AArch64/Round.lean`), inline: the block as a big-endian 64-bit integer in
`x5`, the key schedule at `x14` and the scratch buffer at `x15`. They use
only `x0`–`x17`, so they save nothing, and call nothing.

The scratch buffer: slots 0–5 (bytes `[0, 48)`) are the block's, and slots
6–8 are `init`'s three DES keys, slot 6 `finalize`'s last block `Mₙ`.

* `init` reads the three DES keys (the third is the first for a 16-byte
  key) to slots 6–8, writes their round keys (`roundKeys`, 128 bytes each)
  to `out` (`x2`, advancing), and then encrypts the zero block with them
  (`L`) and doubles it twice, as a 64-bit integer: shifted left by one bit,
  and XORed with `0x1b` masked by the bit shifted out.
* `update` keeps the state pointer in `x1`, the data pointer in `x2` and the
  blocks left in `x3`; each block, `x5` is `C ⊕ Mᵢ`.
* `finalize` forms `Mₙ` in `x5`: `Mₙ* ⊕ K1` for a complete block, else `Mₙ*`
  copied a byte at a time onto zeros in slot 6 (through advancing pointers:
  the model has no register-offset addressing), `0x80` after it, and XORed
  with `K2`.

Only the pointers, `key_len`, `n` and `last_len` can affect timing: the
branches (`cbz`, `cbnz`) are on them and on counters, and the doubling is
masked.
-/

namespace VG.Impl.CmacTripleDes.AArch64

open VG.AArch64

/-! ## `vg_cmac_triple_des_init` -/

/-- The DES key at `[x0 + d]`, as a big-endian integer, to `[x15 + o]`. -/
def keyWord (d o : Nat) : List Instr := [.ldr .x .x5 .x0 d, .rev .x5 .x5, .str .x .x5 .x15 o]

/-- The three DES keys to slots 6–8 (`K3` is `K1` if `key_len` is 16), `x4`
pointing at them and `x3` counting them. -/
def initPre : Prog isa :=
  .seq (.block ([mov .x15 .x3] ++ keyWord 0 48 ++ keyWord 8 56 ++ [.subImm .x .x9 .x1 16]))
    (.seq (.ite (.zero .x .x9) (.block [.ldr .x .x5 .x0 0]) (.block [.ldr .x .x5 .x0 16]))
      (.block [.rev .x5 .x5, .str .x .x5 .x15 64, .addImm .x .x4 .x15 48, .movz .x .x3 3 0]))

/-- The round keys of the DES key at `[x4]` to `[x2]`, and on to the next. -/
def keysBody : List Instr :=
  [.ldr .x .x5 .x4 0] ++ roundKeys ++
    [.addImm .x .x2 .x2 128, .addImm .x .x4 .x4 8, .subImm .x .x3 .x3 1]

/-- The block in `x5`, doubled (`VG.Spec.Cmac.dbl 8`), and stored at
`[x2 + d]` (as bytes). -/
def dbl (d : Nat) : List Instr :=
  [.lsr .x .x6 .x5 63, .movz .x .x7 0 0, .sub .x .x7 .x7 .x6, .movz .x .x11 0x1b 0,
   .logic .and .x .x7 .x7 .x11, .add .x .x5 .x5 .x5, .logic .eor .x .x5 .x5 .x7,
   .rev .x6 .x5, .str .x .x6 .x2 d]

def init : Prog isa :=
  .seq initPre (.seq (.loop (.block keysBody) (.nonzero .x .x3))
    (.seq (.block [.subImm .x .x14 .x2 384, .movz .x .x5 0 0])
      (.seq block (.block (dbl 0 ++ dbl 8)))))

/-! ## `vg_cmac_triple_des_update` -/

/-- `C ⊕ Mᵢ`, as a big-endian integer, into `x5`. -/
def chainIn : List Instr :=
  [.ldr .x .x5 .x1 0, .ldr .x .x6 .x2 0, .logic .eor .x .x5 .x5 .x6, .rev .x5 .x5]

/-- `x5` stored to the state, and on to the next block. -/
def chainOut : List Instr :=
  [.rev .x5 .x5, .str .x .x5 .x1 0, .addImm .x .x2 .x2 8, .subImm .x .x3 .x3 1]

def updBody : Prog isa := .seq (.block chainIn) (.seq block (.block chainOut))

def update : Prog isa :=
  .seq (.block [mov .x14 .x0, mov .x15 .x4])
    (.ite (.zero .x .x3) (.block []) (.loop updBody (.nonzero .x .x3)))

/-! ## `vg_cmac_triple_des_finalize` -/

/-- `Mₙ = Mₙ* ⊕ K1` (`K1` at `x0 + 384`) into `x5`, for a complete last block. -/
def full : List Instr := [.ldr .x .x5 .x2 0, .ldr .x .x6 .x0 384, .logic .eor .x .x5 .x5 .x6]

/-- Slot 6 zeroed, with `x6` pointing at it, `x7` at the last bytes and `x8`
counting them. -/
def zero : List Instr :=
  [.movz .x .x5 0 0, .str .x .x5 .x15 48, .addImm .x .x6 .x15 48, mov .x7 .x2, mov .x8 .x3]

/-- The `x8` (nonzero) bytes at `x7` copied to `x6`, advancing both. -/
def copy : Prog isa :=
  .loop (.block [.ldrb .x9 .x7 0, .strb .x9 .x6 0, .addImm .x .x7 .x7 1, .addImm .x .x6 .x6 1,
    .subImm .x .x8 .x8 1]) (.nonzero .x .x8)

/-- `0x80` after the bytes (at `x6`), and the block XORed with `K2` (at
`x0 + 392`) into `x5`. -/
def padK2 : List Instr :=
  [.movz .x .x9 0x80 0, .strb .x9 .x6 0, .ldr .x .x5 .x15 48, .ldr .x .x6 .x0 392,
   .logic .eor .x .x5 .x5 .x6]

/-- `Mₙ = K2 ⊕ (Mₙ* ‖ 10ʲ)` into `x5`, for a partial last block (`last_len < 8`). -/
def partialBlock : Prog isa :=
  .seq (.block zero) (.seq (.ite (.zero .x .x3) (.block []) copy) (.block padK2))

/-- Sets up the registers; `Mₙ` into `x5`. -/
def finPre : Prog isa :=
  .seq (.block [mov .x14 .x0, mov .x15 .x4, .subImm .x .x9 .x3 8])
    (.ite (.zero .x .x9) (.block full) partialBlock)

def finalize : Prog isa :=
  .seq finPre (.seq (.block [.ldr .x .x6 .x1 0, .logic .eor .x .x5 .x5 .x6, .rev .x5 .x5])
    (.seq block (.block [.rev .x5 .x5, .str .x .x5 .x1 0])))

end VG.Impl.CmacTripleDes.AArch64
