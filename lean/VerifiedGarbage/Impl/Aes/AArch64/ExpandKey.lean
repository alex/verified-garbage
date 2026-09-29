import VerifiedGarbage.Impl.Aes.AArch64.Ctr32

/-!
# The AES key expansion on AArch64

`vg_aes_expand_key(key = x0, key_len = x1, schedule = x2, scratch = x3)`.

FIPS 197 §5.2 (`KEYEXPANSION`), one word at a time, with `SUBWORD` done by
the bitsliced S-box of `Sbox.lean` on the word in the low 32 bits of `q 0`
(as BearSSL's `aes_ct64` does in its `sub_word`; Thomas Pornin, MIT
licence).

* The scratch buffer's base moves to `x5`, which the S-box uses; the
  callee-saved registers are saved in its slots 48–58, and the round
  constant is kept in slot 59.
* The key is copied into the schedule 8 bytes at a time (16, 24 and 32 are
  multiples of 8); the last word copied, `w[Nk − 1]`, is left in `q 0`.
* Word `i` (from `Nk` on) is computed with `x0` at `w[i − Nk]`, `x2` at
  `w[i]`, `x3 = Nk`, `x1 = i mod Nk`, `x4` the words left, and `q 0 =
  w[i − 1]`. Every branch is on these, which depend only on `key_len`; the
  key's bytes only ever reach the S-box's registers and memory.
-/

namespace VG.Impl.Aes.AArch64

open VG.AArch64

/-- The slot of the round constant. -/
def rconSlot : Nat := 59

/-- Copy the key (`x4` bytes at `x0`, a multiple of 8) to `x2`. -/
def copyBody : List Instr :=
  [.ldr .x (q 0) .x0 0, .str .x (q 0) .x2 0, .addImm .x .x0 .x0 8, .addImm .x .x2 .x2 8,
   .subImm .x .x4 .x4 8]

/-- After the copy (`x2` at `w[Nk]`, the last 8 bytes copied in `q 0`):
`q 0 := w[Nk − 1]`, `x0 := ` the schedule, `x3 := Nk`, `x1 := 0`, `x4 :=
4 (Nr + 1) − Nk = 3 Nk + 28` words left, and the round constant 1. -/
def wordSetup : List Instr :=
  [lsrI (q 0) (q 0) 32, .sub .x .x0 .x2 .x1, lsrI .x3 .x1 2, .movz .x .x1 0 0,
   .add .x .x4 .x3 .x3, .add .x .x4 .x4 .x3, .addImm .x .x4 .x4 28,
   .movz .x (q 1) 1 0, stS rconSlot (q 1)]

/-- The S-box on each byte of `q 0` (and of the other words). -/
def subAll : List Instr := toBs ++ sboxCode ++ fromBs

/-- After `subAll`: `q 0 := ROTWORD(q 0) ⊕ Rcon` (on the low 32 bits), and
the round constant times `x` (without a branch: `{1b}` times its bit 7 is
XORed in). -/
def rotTail : List Instr :=
  [.ror .w (q 0) (q 0) 8, ldS (q 1) rconSlot, .logic .eor .w (q 0) (q 0) (q 1),
   lsrI (q 2) (q 1) 7, .movz .x (q 3) 0x1b 0, .mul .x (q 2) (q 2) (q 3),
   .lsl .x (q 1) (q 1) 1, eorR (q 1) (q 1) (q 2), .movz .x (q 3) 0xff 0, andR (q 1) (q 1) (q 3),
   stS rconSlot (q 1)]

/-- `q 0 := SUBWORD(ROTWORD(q 0)) ⊕ Rcon`. -/
def rotWordStep : List Instr := subAll ++ rotTail

/-- Word `i`: `temp := w[i − 1]`, transformed if `i mod Nk = 0`, or if
`Nk = 8` and `i mod Nk = 4`; `w[i] := w[i − Nk] ⊕ temp`; and on to `i + 1`. -/
def wordBody : Prog isa :=
  .seq (.ite (.zero .x .x1) (.block rotWordStep)
      (.seq (.block [.subImm .x (q 1) .x1 4, .subImm .x (q 2) .x3 8, orrR (q 1) (q 1) (q 2)])
        (.ite (.zero .x (q 1)) (.block subAll) (.block []))))
    (.seq (.block [.ldr .w (q 1) .x0 0, .logic .eor .w (q 0) (q 0) (q 1), .str .w (q 0) .x2 0,
        .addImm .x .x0 .x0 4, .addImm .x .x2 .x2 4, .addImm .x .x1 .x1 1, .sub .x (q 1) .x1 .x3])
      (.seq (.ite (.zero .x (q 1)) (.block [.movz .x .x1 0 0]) (.block []))
        (.block [.subImm .x .x4 .x4 1])))

def expandKey : Prog isa :=
  .seq (.block ([movR sb .x3] ++ saveRegs ++ [movR .x4 .x1]))
    (.seq (.loop (.block copyBody) (.nonzero .x .x4))
      (.seq (.block wordSetup)
        (.seq (.loop wordBody (.nonzero .x .x4)) (.block restoreRegs))))

end VG.Impl.Aes.AArch64
