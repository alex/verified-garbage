import VerifiedGarbage.Impl.CmacTripleDes.Arm.Round

/-!
# TDEA-CMAC (3DES-CMAC): 32-bit ARM implementation

`vg_cmac_triple_des_init(key = r0, key_len = r1, out = r2, scratch = r3)`,
`vg_cmac_triple_des_update(schedule = r0, state = r1, data = r2, n = r3, scratch = [sp])`
and `vg_cmac_triple_des_finalize(key = r0, state = r1, last = r2, last_len = r3, scratch = [sp])`
(see `VG.Spec.Cmac.tdesInitContract` and the others). Each encrypts blocks
with `block` (`Arm/Round.lean`), inline: the block as a big-endian 64-bit
integer in `r0:r1` (its high and low words), the key schedule at `r9` and
the scratch buffer at `r10`. The block uses every register, so the
functions keep their pointers and counts in the scratch buffer.

The scratch buffer: words 0–12 (bytes `[0, 52)`) are the block's; bytes
`[52, 88)` hold our caller's callee-saved registers `r4`–`r11` and `lr`;
`[88, 112)` are `init`'s three DES keys (each as its high and low words);
`[112, 124)` the output or state pointer, the data pointer and a count; and
`[124, 132)` `finalize`'s last block `Mₙ`.

* `init` reads the three DES keys (the third is the first for a 16-byte
  key), writes their round keys (`roundKeys`, 128 bytes each) to `out`
  (`r2`, advancing), and then encrypts the zero block with them (`L`) and
  doubles it twice, as a 64-bit integer: shifted left by one bit, and XORed
  with `0x1b` masked by the bit shifted out.
* `update` reloads the state and data pointers each block; after the
  block, it loads them and the count before it stores the state, and stores
  them back after.
* `finalize` forms `Mₙ` in `r4:r5` as little-endian words: `Mₙ* ⊕ K1` for a
  complete block, else `Mₙ*` copied a byte at a time onto zeros (through
  advancing pointers: the model has no register-offset addressing), `0x80`
  after it, and XORed with `K2`; it saves the state pointer only then.

Only the pointers, `key_len`, `n` and `last_len` can affect timing: the
branches are on them and on counters, and the doubling is masked.
-/

namespace VG.Impl.CmacTripleDes.Arm

open VG.Arm

/-- Our caller's callee-saved registers, and where they are saved (`r10`,
the base of the restore, last). -/
def saved : List (Reg × Nat) :=
  [(.r4, 52), (.r5, 56), (.r6, 60), (.r7, 64), (.r8, 68), (.r9, 72), (.r11, 76), (.lr, 80), (.r10, 84)]

/-- Saves the registers to the scratch buffer at `scr`. -/
def save (scr : Reg) : List Instr := saved.map fun (r, d) => .str r scr d

/-- Restores the registers, with `r10` (restored last) the scratch buffer. -/
def restore : List Instr := saved.map fun (r, d) => .ldr r .r10 d

/-! ## `vg_cmac_triple_des_init` -/

/-- The word at `[r0 + d]`, byte-reversed, to `[r10 + o]`. -/
def keyWord (d o : Nat) : List Instr := [.ldr .r4 .r0 d, .rev .r4 .r4, .str .r4 .r10 o]

/-- Saves the registers, and the three DES keys to `[r10 + 88]` (`K3` is `K1`
if `key_len` is 16), with `r4` pointing at them and `r5` counting them. -/
def initPre : Prog isa :=
  .seq (.block (save .r3 ++ [mov .r10 .r3] ++ keyWord 0 88 ++ keyWord 4 92 ++ keyWord 8 96 ++ keyWord 12 100 ++
      [.cmp .r1 (.imm 16)]))
    (.seq (.ite .eq (.block [.ldr .r4 .r0 0, .ldr .r5 .r0 4]) (.block [.ldr .r4 .r0 16, .ldr .r5 .r0 20]))
      (.block [.rev .r4 .r4, .rev .r5 .r5, .str .r4 .r10 104, .str .r5 .r10 108,
        .dp .add .r4 .r10 (.imm 88), .mov .r5 (.imm 3)]))

/-- The round keys of the DES key at `[r4]` to `[r2]`, and on to the next. -/
def keysBody : List Instr :=
  [.ldr .r0 .r4 0, .ldr .r1 .r4 4] ++ roundKeys ++
    [.dp .add .r2 .r2 (.imm 128), .dp .add .r4 .r4 (.imm 8), .subs .r5 .r5 (.imm 1)]

/-- The block in `r0:r1`, doubled (`VG.Spec.Cmac.dbl 8`), and stored at
`[r2 + d]` (as bytes). -/
def dbl (d : Nat) : List Instr :=
  [.mov .r3 (.shifted .r0 .lsr 31), .mov .r4 (.imm 0), .dp .sub .r3 .r4 (.reg .r3), .dp .and .r3 .r3 (.imm 0x1b),
   .mov .r4 (.shifted .r1 .lsr 31), .mov .r0 (.shifted .r0 .lsl 1), .dp .orr .r0 .r0 (.reg .r4),
   .mov .r1 (.shifted .r1 .lsl 1), .dp .eor .r1 .r1 (.reg .r3),
   .rev .r3 .r0, .str .r3 .r2 d, .rev .r3 .r1, .str .r3 .r2 (d + 4)]

def init : Prog isa :=
  .seq initPre (.seq (.loop (.block keysBody) .ne)
    (.seq (.block [.str .r2 .r10 112, .dp .sub .r9 .r2 (.imm 384), .mov .r0 (.imm 0), .mov .r1 (.imm 0)])
      (.seq block (.block ([.ldr .r2 .r10 112] ++ dbl 0 ++ dbl 8 ++ restore)))))

/-! ## `vg_cmac_triple_des_update` -/

/-- Saves the registers and the arguments; Z is set if there are no blocks. -/
def updPre : List Instr :=
  [.ldrSp .r12 0] ++ save .r12 ++
  [mov .r10 .r12, mov .r9 .r0, .str .r1 .r10 112, .str .r2 .r10 116, .str .r3 .r10 120, .cmp .r3 (.imm 0)]

/-- `C ⊕ Mᵢ`, as a big-endian integer, into `r0:r1`. -/
def chainIn : List Instr :=
  [.ldr .r4 .r10 112, .ldr .r5 .r10 116, .ldr .r0 .r4 0, .ldr .r1 .r4 4, .ldr .r2 .r5 0, .ldr .r3 .r5 4,
   .dp .eor .r0 .r0 (.reg .r2), .dp .eor .r1 .r1 (.reg .r3), .rev .r0 .r0, .rev .r1 .r1]

/-- `r0:r1` stored to the state, and on to the next block (Z is set when none
are left). -/
def chainOut : List Instr :=
  [.ldr .r4 .r10 112, .ldr .r5 .r10 116, .ldr .r6 .r10 120, .rev .r0 .r0, .rev .r1 .r1,
   .str .r0 .r4 0, .str .r1 .r4 4, .dp .add .r5 .r5 (.imm 8), .dp .sub .r6 .r6 (.imm 1),
   .str .r4 .r10 112, .str .r5 .r10 116, .str .r6 .r10 120, .cmp .r6 (.imm 0)]

def updBody : Prog isa := .seq (.block chainIn) (.seq block (.block chainOut))

def update : Prog isa :=
  .seq (.block updPre) (.seq (.ite .eq (.block []) (.loop updBody .ne)) (.block restore))

/-! ## `vg_cmac_triple_des_finalize` -/

/-- `Mₙ = Mₙ* ⊕ K1` (`K1` at `r9 + 384`) into `r4:r5`, for a complete last block. -/
def full : List Instr :=
  [.ldr .r4 .r2 0, .ldr .r5 .r2 4, .ldr .r6 .r9 384, .ldr .r7 .r9 388, .dp .eor .r4 .r4 (.reg .r6),
   .dp .eor .r5 .r5 (.reg .r7)]

/-- `[r10 + 124]` zeroed, with `r6` pointing at it, `r7` at the last bytes and
`r8` counting them; Z is set if `last_len` is 0. -/
def zero : List Instr :=
  [.mov .r4 (.imm 0), .str .r4 .r10 124, .str .r4 .r10 128, .dp .add .r6 .r10 (.imm 124), mov .r7 .r2,
   mov .r8 .r3, .cmp .r3 (.imm 0)]

/-- The `r8` (nonzero) bytes at `r7` copied to `r6`, advancing both. -/
def copy : Prog isa :=
  .loop (.block [.ldrb .r4 .r7 0, .strb .r4 .r6 0, .dp .add .r7 .r7 (.imm 1), .dp .add .r6 .r6 (.imm 1),
    .subs .r8 .r8 (.imm 1)]) .ne

/-- `0x80` after the bytes (at `r6`), and the block XORed with `K2` (at
`r9 + 392`) into `r4:r5`. -/
def padK2 : List Instr :=
  [.mov .r4 (.imm 0x80), .strb .r4 .r6 0, .ldr .r4 .r10 124, .ldr .r5 .r10 128, .ldr .r6 .r9 392,
   .ldr .r7 .r9 396, .dp .eor .r4 .r4 (.reg .r6), .dp .eor .r5 .r5 (.reg .r7)]

/-- `Mₙ = K2 ⊕ (Mₙ* ‖ 10ʲ)` into `r4:r5`, for a partial last block (`last_len < 8`). -/
def partialBlock : Prog isa :=
  .seq (.block zero) (.seq (.ite .eq (.block []) copy) (.block padK2))

/-- Saves the registers and sets them up; `Mₙ` into `r4:r5`. -/
def finPre : Prog isa :=
  .seq (.block ([.ldrSp .r12 0] ++ save .r12 ++ [mov .r10 .r12, mov .r9 .r0, .cmp .r3 (.imm 8)]))
    (.ite .eq (.block full) partialBlock)

/-- The state pointer saved, and `C ⊕ Mₙ` as a big-endian integer into `r0:r1`. -/
def finMid : List Instr :=
  [.str .r1 .r10 112, .ldr .r6 .r1 0, .ldr .r7 .r1 4, .dp .eor .r4 .r4 (.reg .r6), .dp .eor .r5 .r5 (.reg .r7),
   .rev .r0 .r4, .rev .r1 .r5]

def finalize : Prog isa :=
  .seq finPre (.seq (.block finMid)
    (.seq block (.block ([.ldr .r2 .r10 112, .rev .r0 .r0, .rev .r1 .r1, .str .r0 .r2 0, .str .r1 .r2 4] ++
      restore))))

end VG.Impl.CmacTripleDes.Arm
