import VerifiedGarbage.Impl.Aes.Arm.Ctr32

/-!
# The AES key expansion on ARMv7

`vg_aes_expand_key(key = r0, key_len = r1, schedule = r2, scratch = r3)`.

FIPS 197 §5.2 (`KEYEXPANSION`), one word at a time, with `SUBWORD` done by
the bitsliced S-box of `Sbox.lean` on the word in `q 0` (as BearSSL's
`aes_ct` does in its `sub_word`; Thomas Pornin, MIT licence).

* The callee-saved registers are saved in slots 32–40 of the scratch
  buffer, whose base then moves to `r8`, which the S-box uses; the round
  constant is kept in slot 41.
* The key is copied into the schedule 4 bytes at a time; the last word
  copied, `w[Nk − 1]`, is left in `q 0`.
* Word `i` (from `Nk` on) is computed with `r9` at `w[i − Nk]`, `r10` at
  `w[i]`, `r11 = i mod Nk`, `r12 = Nk`, `lr` the words left, and `q 0 =
  w[i − 1]`. The S-box uses every register but `r8` and `r9`, so `r10`–`r12`
  and `lr` are stored in slots 42–45 around it (`subAll`). Every branch is
  on these, which depend only on `key_len`; the key's bytes only ever
  reach the S-box's registers and memory.
-/

namespace VG.Impl.Aes.Arm

open VG.Arm

/-- The slot of the round constant. -/
def rconSlot : Nat := 41

/-- The slots of `r10`–`r12` and `lr` around the S-box. -/
def loopRegs : List (Reg × Nat) := [(.r10, 42), (.r11, 43), (.r12, 44), (.lr, 45)]

/-- Copy the key (`lr` bytes at `r9`, a multiple of 4) to `r10`. -/
def copyBody : List Instr :=
  [.ldr (q 0) .r9 0, .str (q 0) .r10 0, .dp .add .r9 .r9 (.imm 4), .dp .add .r10 .r10 (.imm 4),
   .subs .lr .lr (.imm 4)]

/-- After the copy (`r10` at `w[Nk]`, `q 0 = w[Nk − 1]`): `r9 := ` the
schedule, `r12 := Nk`, `r11 := 0`, `lr := 4 (Nr + 1) − Nk = 3 Nk + 28`
words left, and the round constant 1. -/
def wordSetup : List Instr :=
  [.dp .sub .r9 .r10 (.reg .r1), .mov .r12 (lsrOp .r1 2), .mov .r11 (.imm 0),
   .dp .add .lr .r12 (.shifted .r12 .lsl 1), .dp .add .lr .lr (.imm 28),
   .mov (q 1) (.imm 1), stS rconSlot (q 1)]

/-- The S-box on each byte of `q 0` (and of the other words), keeping the
loop registers in their slots meanwhile. -/
def subAll : List Instr :=
  loopRegs.map (fun (r, k) => stS k r) ++ ortho ++ sboxCode ++ ortho ++
  loopRegs.map (fun (r, k) => ldS r k)

/-- After `subAll`: `q 0 := ROTWORD(q 0) ⊕ Rcon`, and the round constant
times `x` (without a branch: `{1b}` times its bit 7 is XORed in). -/
def rotTail : List Instr :=
  [.mov (q 0) (rorOp (q 0) 8), ldS (q 1) rconSlot, eorR (q 0) (q 0) (q 1),
   .mov (q 2) (lsrOp (q 1) 7), .mov (q 3) (.imm 0x1b), .mul (q 2) (q 2) (q 3),
   .mov (q 1) (.shifted (q 1) .lsl 1), eorR (q 1) (q 1) (q 2), .dp .and (q 1) (q 1) (.imm 0xff),
   stS rconSlot (q 1)]

/-- `q 0 := SUBWORD(ROTWORD(q 0)) ⊕ Rcon`. -/
def rotWordStep : List Instr := subAll ++ rotTail

/-- Word `i`: `temp := w[i − 1]`, transformed if `i mod Nk = 0`, or if
`Nk = 8` and `i mod Nk = 4`; `w[i] := w[i − Nk] ⊕ temp`; and on to `i + 1`. -/
def wordBody : Prog isa :=
  .seq (.block [.cmp .r11 (.imm 0)])
    (.seq (.ite .eq (.block rotWordStep)
        (.seq (.block [.dp .sub (q 1) .r11 (.imm 4), .dp .sub (q 2) .r12 (.imm 8),
            .dp .orr (q 1) (q 1) (.reg (q 2)), .cmp (q 1) (.imm 0)])
          (.ite .eq (.block subAll) (.block []))))
      (.seq (.block [.ldr (q 1) .r9 0, eorR (q 0) (q 0) (q 1), .str (q 0) .r10 0,
          .dp .add .r9 .r9 (.imm 4), .dp .add .r10 .r10 (.imm 4), .dp .add .r11 .r11 (.imm 1),
          .cmp .r11 (.reg .r12)])
        (.seq (.ite .eq (.block [.mov .r11 (.imm 0)]) (.block []))
          (.block [.subs .lr .lr (.imm 1)]))))

def expandKey : Prog isa :=
  .seq (.block (saveRegs .r3 ++ [movR sb .r3, movR .r9 .r0, movR .r10 .r2, movR .lr .r1]))
    (.seq (.loop (.block copyBody) .ne)
      (.seq (.block wordSetup)
        (.seq (.loop wordBody .ne) (.block (movR .r12 sb :: restoreRegs .r12)))))

end VG.Impl.Aes.Arm
