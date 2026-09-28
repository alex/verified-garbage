import VerifiedGarbage.TCB.X86_64.Print

/-!
# Semantics tests for the x86-64 SSE2 instructions

Each expected value was computed on an x86-64 CPU, by the same instruction
through its SSE2 intrinsic (`_mm_add_epi32`, `_mm_shuffle_epi32`, …; the
shifts by a count in a register, whose semantics are those of the immediate
form), and is compared with the model's result on the same inputs. This
tests the transcription of the SDM's pseudocode (in particular which
doubleword is which), which review of the TCB would otherwise have to
catch by eye.
-/

namespace VG.Test.Sse

open X86_64

def a : BitVec 128 := 0x89abcdef01234567fedcba9876543210#128
def b : BitVec 128 := 0xffffffff800000007fffffff12345678#128

/-- A state with `a` in `xmm0` and `b` in `xmm1`, and 16 bytes `17 i + 3` at
address `0x100`, readable. -/
def s : State where
  gpr r := if r = .rdi then 0x100 else 0
  cf := none
  zf := none
  sf := none
  of := none
  xmm r := if r = .xmm0 then a else if r = .xmm1 then b else 0
  mem addr := if 0x100 ≤ addr.toNat ∧ addr.toNat < 0x110 then
    BitVec.ofNat 8 (17 * (addr.toNat - 0x100) + 3) else 0
  rd := [⟨0x100, 16⟩]
  wr := [⟨0x200, 16⟩]

/-- `xmm0` after `op xmm0, xmm1`. -/
def bin (op : XBinOp) : BitVec 128 := ((XOp.bin op .xmm0 .xmm1).exec s).xmm .xmm0

#guard bin .movdqa == b
#guard bin .paddd == 0x89abcdee812345677edcba9788888888#128
#guard bin .pxor == 0x76543210812345678123456764606468#128
#guard bin .por == 0xffffffff81234567ffffffff76747678#128
#guard bin .punpckldq == 0x7ffffffffedcba981234567876543210#128
#guard bin .punpckhdq == 0xffffffff89abcdef8000000001234567#128
#guard bin .punpcklqdq == 0x7fffffff12345678fedcba9876543210#128
#guard bin .punpckhqdq == 0xffffffff8000000089abcdef01234567#128

/-- `xmm0` after `op xmm0, n`. -/
def shift (op : XShiftOp) (n : BitVec 8) : BitVec 128 := ((XOp.shift op .xmm0 n).exec s).xmm .xmm0

#guard shift .pslld 7 == 0xd5e6f78091a2b3806e5d4c002a190800#128
#guard shift .psrld 25 == 0x00000044000000000000007f0000003b#128
#guard shift .pslld 31 == 0x80000000800000000000000000000000#128
#guard shift .psrld 32 == 0
#guard shift .pslld 255 == 0

/-- `xmm1` after `pshufd xmm1, xmm0, order`. -/
def shuf (order : BitVec 8) : BitVec 128 := ((XOp.pshufd .xmm1 .xmm0 order).exec s).xmm .xmm1

#guard shuf 0x1b == 0x76543210fedcba980123456789abcdef#128
#guard shuf 0x93 == 0x01234567fedcba987654321089abcdef#128
#guard shuf 0x00 == 0x76543210765432107654321076543210#128

-- Only the destination changes.
#guard ((XOp.bin .paddd .xmm0 .xmm1).exec s).xmm .xmm1 == b
#guard ((XOp.pshufd .xmm1 .xmm0 0x1b).exec s).xmm .xmm0 == a

-- `movdqu`: little-endian, within the permitted regions only.
#guard ((exec (.movdquLoad .xmm2 { base := .rdi }) s).map (·.xmm .xmm2)) ==
  some 0x02f1e0cfbead9c8b7a69584736251403#128
#guard (exec (.movdquLoad .xmm2 { base := .rdi, disp := 1 }) s).isNone
#guard (exec (.movdquStore { base := .rdi } .xmm0) s).isNone
#guard ((exec (.movdquStore { base := .rdi, disp := 0x100 } .xmm0) s).map
  (·.mem.readW 0x200 128)) == some a
#guard (exec (.movdquStore { base := .rdi, disp := 0x101 } .xmm0) s).isNone

/-! ## Printing -/

#guard printer.instr (.movdquLoad .xmm0 { base := .rdi, disp := 16 }) ==
  ["movdqu xmm0, XMMWORD PTR [rdi+16]"]
#guard printer.instr (.movdquStore { base := .rsi, index := some .rcx, scale := 8 } .xmm15) ==
  ["movdqu XMMWORD PTR [rsi+rcx*8], xmm15"]
#guard printer.instr (.xop (.bin .movdqa .xmm1 .xmm2)) == ["movdqa xmm1, xmm2"]
#guard printer.instr (.xop (.bin .paddd .xmm3 .xmm4)) == ["paddd xmm3, xmm4"]
#guard printer.instr (.xop (.bin .pxor .xmm5 .xmm6)) == ["pxor xmm5, xmm6"]
#guard printer.instr (.xop (.bin .por .xmm7 .xmm8)) == ["por xmm7, xmm8"]
#guard printer.instr (.xop (.bin .punpckldq .xmm9 .xmm10)) == ["punpckldq xmm9, xmm10"]
#guard printer.instr (.xop (.bin .punpckhdq .xmm11 .xmm12)) == ["punpckhdq xmm11, xmm12"]
#guard printer.instr (.xop (.bin .punpcklqdq .xmm13 .xmm14)) == ["punpcklqdq xmm13, xmm14"]
#guard printer.instr (.xop (.bin .punpckhqdq .xmm0 .xmm15)) == ["punpckhqdq xmm0, xmm15"]
#guard printer.instr (.xop (.shift .pslld .xmm1 7)) == ["pslld xmm1, 7"]
#guard printer.instr (.xop (.shift .psrld .xmm2 25)) == ["psrld xmm2, 25"]
#guard printer.instr (.xop (.pshufd .xmm3 .xmm4 0x93)) == ["pshufd xmm3, xmm4, 147"]

-- SSE2 is in the x86-64 baseline.
#guard isa.requires (.xop (.pshufd .xmm3 .xmm4 0x93)) == []

end VG.Test.Sse
