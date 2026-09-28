import VerifiedGarbage.Impl.Aes.X86_64.Ctr32

/-!
# The AES key expansion on x86-64

`vg_aes_expand_key(key = rdi, key_len = rsi, schedule = rdx, scratch = rcx)`.

FIPS 197 §5.2 (`KEYEXPANSION`), one word at a time, with `SUBWORD` done by
the bitsliced S-box of `Sbox.lean` on the word in the low 32 bits of `q 0`
(as BearSSL's `aes_ct64` does in its `sub_word`; Thomas Pornin, MIT
licence).

* `r9` is the scratch buffer; the callee-saved registers are saved in its
  slots 48–53, and the round constant is kept in slot 54.
* The key is copied into the schedule 8 bytes at a time (16, 24 and 32 are
  multiples of 8).
* Word `i` (from `Nk` on) is computed with `rdx` at `w[i]`, `rsi = -4 Nk`
  (so `[rdx + rsi]` is `w[i − Nk]`), `rdi = 4 (i mod Nk) − 4 Nk` and `r8`
  the words left. Every branch is on these, which depend only on `key_len`;
  the key's bytes only ever reach `rax`, the S-box's registers and memory.
-/

namespace VG.Impl.Aes.X86_64

open VG.X86_64

/-- The slot of the round constant. -/
def rconSlot : Nat := 54

/-- Copy the key (`rsi` bytes at `rdi`, a multiple of 8) to `rdx`. -/
def copyBody : List Instr :=
  [.mov .rax (.mem (at_ .rdi 0)), .store (at_ .rdx 0) .rax, .alu .add .rdi (.imm 8),
   .alu .add .rdx (.imm 8), .alu .sub .rsi (.imm 8)]

/-- After the copy (`rsi = 0`, `r8 = 4 Nk`): `rsi := -4 Nk`, `rdi := rsi`,
`r8 := 4 (Nr + 1) − Nk = 3 Nk + 28` words left, and the round constant 1. -/
def wordSetup : List Instr :=
  [.alu .sub .rsi (.reg .r8), movR .rdi .rsi, shrI .r8 2, movR .rax .r8,
   .alu .add .r8 (.reg .r8), .alu .add .r8 (.reg .rax), .alu .add .r8 (.imm 28),
   imm .rax 1, st rconSlot .rax]

/-- The S-box on each byte of `q 0` (and of the other words). -/
def subAll : List Instr := toBs ++ sboxCode ++ fromBs

/-- After `subAll`: `rax := ROTWORD(rax) ⊕ Rcon` (on the low 32 bits), and
the round constant times `x` (without a branch: `{1b}` is XORed in under a
mask made from bit 7). -/
def rotTail : List Instr :=
  [.shift32 .ror .rax 8, .alu .xor .rax (.mem (slotAt sb rconSlot)),
   movS (q 1) rconSlot, movR (q 2) (q 1), shrI (q 2) 7, imm (q 3) 0, .alu .sub (q 3) (.reg (q 2)),
   .alu .and (q 3) (.imm 0x1b), .alu .add (q 1) (.reg (q 1)), xorR (q 1) (q 3),
   .alu .and (q 1) (.imm 0xff), st rconSlot (q 1)]

/-- `rax := SUBWORD(ROTWORD(rax)) ⊕ Rcon`. -/
def rotWordStep : List Instr := subAll ++ rotTail

/-- Word `i`: `temp := w[i − 1]`, transformed if `i mod Nk = 0`, or if
`Nk = 8` and `i mod Nk = 4`; `w[i] := w[i − Nk] ⊕ temp`; and on to `i + 1`
(ZF is set after the last word). -/
def wordBody : Prog isa :=
  .seq (.block [.mov32 .rax (.mem { base := .rdx, disp := -4 }), .alu .cmp .rdi (.reg .rsi)])
    (.seq (.ite .e (.block rotWordStep)
        (.seq (.block [.alu .cmp .rdi (.imm (-16))])
          (.ite .e (.seq (.block [.alu .cmp .rsi (.imm (-32))]) (.ite .e (.block subAll) (.block [])))
            (.block []))))
      (.seq (.block [.alu32 .xor .rax (.mem { base := .rdx, index := some .rsi }),
          .store32 (at_ .rdx 0) .rax, .alu .add .rdx (.imm 4), .alu .add .rdi (.imm 4)])
        (.seq (.ite .e (.block [movR .rdi .rsi]) (.block []))
          (.block [.alu .sub .r8 (.imm 1)]))))

def expandKey : Prog isa :=
  .seq (.block ([movR .r9 .rcx] ++ saveRegs ++ [movR .r8 .rsi]))
    (.seq (.loop (.block copyBody) .ne)
      (.seq (.block wordSetup)
        (.seq (.loop wordBody .ne) (.block restoreRegs))))

end VG.Impl.Aes.X86_64
