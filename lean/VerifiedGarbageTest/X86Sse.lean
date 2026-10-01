import VerifiedGarbage.TCB.X86.Print

/-!
# IA-32 legacy SIMD transcription tests

These instruction-level inputs and expected results are reused from
`VerifiedGarbageTest/X86_64Sse.lean`, where they were cross-checked with
native intrinsics. The legacy 128-bit SDM operations are identical in
32-bit and 64-bit modes; register availability and MOVD differ, tested
here separately. These are ISA transcription tests, not new primitive
known-answer vectors. Tests cover aliasing, byte/lane order, oversized
immediates, memory permissions, instruction printing and CPU requirements.
-/

namespace VG.Test.X86Sse

open X86

def a : BitVec 128 := 0x89abcdef01234567fedcba9876543210#128
def b : BitVec 128 := 0xffffffff800000007fffffff12345678#128
/-- The `pshufb` mask that reverses the bytes of each doubleword. -/
def c : BitVec 128 := 0x0c0d0e0f08090a0b0405060700010203#128

def s : State where
  gpr r := if r = .edi then 0x100 else if r = .eax then 0xffffffff else 0
  cf := some true
  zf := some false
  sf := some true
  of := some false
  xmm r := if r = .xmm0 then a else if r = .xmm1 then b else if r = .xmm2 then c else 0
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
#guard bin .pshufb == 0x0000000000101010890000005498dc67#128
#guard bin .sha256msg1 == 0x71a8b4dd3e8111b31e5ca90676d443a1#128
#guard bin .sha256msg2 == 0x53d29532d27aee3bff1cba9776748210#128
#guard bin .pand == 0x89abcdef000000007edcba9812141210#128
#guard bin .pandn == 0x76543210800000000123456700204468#128
#guard bin .aesenc == 0xd8908bc5e4ae3f56c95bfb9bd0b4a271#128
#guard bin .aesenclast == 0x8379dc203b20bd85479d91b9b512a2b2#128


/-- `xmm1` after `op xmm1, xmm0`. -/
def binRev (op : XBinOp) : BitVec 128 := ((XOp.bin op .xmm1 .xmm0).exec s).xmm .xmm1

#guard binRev .sha256msg1 == 0x22a233b29fffffff91001fff21343677#128
#guard binRev .sha256msg2 == 0x246c964d5082e17c1f685f12dc537edc#128

-- `pshufb xmm0, xmm2` reverses the bytes of each doubleword.
#guard ((XOp.bin .pshufb .xmm0 .xmm2).exec s).xmm .xmm0 ==
  0xefcdab896745230198badcfe10325476#128

-- `sha256rnds2` reads `xmm0` (here `a`), including when it is the destination.
#guard ((XOp.sha256rnds2 .xmm1 .xmm2).exec s).xmm .xmm1 == 0x3aa0667b764849a77d081e7962f81bbd#128
#guard ((XOp.sha256rnds2 .xmm0 .xmm1).exec s).xmm .xmm0 == 0xdf90e07e06788845012d205c7defffbe#128


/-- `xmm0` after `palignr xmm0, xmm1, n`. -/
def align (n : BitVec 8) : BitVec 128 := ((XOp.palignr .xmm0 .xmm1 n).exec s).xmm .xmm0

#guard align 4 == 0x76543210ffffffff800000007fffffff#128
#guard align 0 == b
#guard align 16 == a
#guard align 20 == 0x0000000089abcdef01234567fedcba98#128
#guard align 31 == 0x00000000000000000000000000000089#128
#guard align 32 == 0
#guard align 255 == 0

/-- `xmm1` after `aeskeygenassist xmm1, src, rcon`. -/
def keygen (src : XReg) (rcon : BitVec 8) : BitVec 128 :=
  ((XOp.aeskeygenassist .xmm1 src rcon).exec s).xmm .xmm1

#guard keygen .xmm0 0x00 == 0xdfa762bda762bddf46bb86f4bb86f446#128
#guard keygen .xmm0 0x01 == 0xdfa762bca762bddf46bb86f5bb86f446#128
#guard keygen .xmm1 0x36 == 0x161616201616161616d21620d2161616#128
#guard keygen .xmm1 0xff == 0x161616e91616161616d216e9d2161616#128

/-- `xmm0` after `pclmulqdq xmm0, xmm1, sel`. -/
def clmulSel (sel : BitVec 8) : BitVec 128 := ((XOp.pclmulqdq .xmm0 .xmm1 sel).exec s).xmm .xmm0

#guard clmulSel 0x00 == 0x2ada34c44d51ecf6d3aacfb2b4211780#128
#guard clmulSel 0x01 == 0x3c4ca252f17b911ec53c5924080b6a68#128
#guard clmulSel 0x10 == 0x55b469880716253416e608f800000000#128
#guard clmulSel 0x11 == 0x789944a53cad9e8f80709e6e80000000#128
-- Only bits 0 and 4 of the immediate select.
#guard clmulSel 0xee == clmulSel 0x00
-- The largest product: bit 127 is always 0.
#guard clmul (-1) (-1) == 0x55555555555555555555555555555555#128

/-- `xmm0` after `op xmm0, n`. -/
def shift (op : XShiftOp) (n : BitVec 8) : BitVec 128 := ((XOp.shift op .xmm0 n).exec s).xmm .xmm0

#guard shift .pslld 7 == 0xd5e6f78091a2b3806e5d4c002a190800#128
#guard shift .psrld 25 == 0x00000044000000000000007f0000003b#128
#guard shift .pslld 31 == 0x80000000800000000000000000000000#128
#guard shift .psrld 32 == 0
#guard shift .pslld 255 == 0
#guard shift .psllq 13 == 0x79bde02468ace00097530eca86420000#128
#guard shift .psrlq 13 == 0x00044d5e6f78091a0007f6e5d4c3b2a1#128
#guard shift .psllq 63 == 0x80000000000000000000000000000000#128
#guard shift .psrlq 63 == 0x00000000000000010000000000000001#128
#guard shift .psllq 64 == 0
#guard shift .psrlq 255 == 0
#guard shift .pslldq 4 == 0x01234567fedcba987654321000000000#128
#guard shift .psrldq 4 == 0x0000000089abcdef01234567fedcba98#128
#guard shift .pslldq 15 == 0x10000000000000000000000000000000#128
#guard shift .psrldq 15 == 0x00000000000000000000000000000089#128
#guard shift .pslldq 16 == 0
#guard shift .psrldq 16 == 0
#guard shift .pslldq 255 == 0

/-- `xmm1` after `pshufd xmm1, xmm0, order`. -/
def shuf (order : BitVec 8) : BitVec 128 := ((XOp.pshufd .xmm1 .xmm0 order).exec s).xmm .xmm1

#guard shuf 0x1b == 0x76543210fedcba980123456789abcdef#128
#guard shuf 0x93 == 0x01234567fedcba987654321089abcdef#128
#guard shuf 0x00 == 0x76543210765432107654321076543210#128

-- Only the destination changes.
#guard ((XOp.bin .paddd .xmm0 .xmm1).exec s).xmm .xmm1 == b
#guard ((XOp.pshufd .xmm1 .xmm0 0x1b).exec s).xmm .xmm0 == a

-- `movdqu`: little-endian, within the permitted regions only.
#guard ((exec (.movdquLoad .xmm2 { base := .edi }) s).map (·.xmm .xmm2)) ==
  some 0x02f1e0cfbead9c8b7a69584736251403#128
#guard (exec (.movdquLoad .xmm2 { base := .edi, disp := 1 }) s).isNone
#guard (exec (.movdquStore { base := .edi } .xmm0) s).isNone
#guard ((exec (.movdquStore { base := .edi, disp := 0x100 } .xmm0) s).map
  (·.mem.readW 0x200 128)) == some a
#guard (exec (.movdquStore { base := .edi, disp := 0x101 } .xmm0) s).isNone


-- MOVD r32 zeroes the other 96 bits, including when the destination was nonzero.
#guard ((XOp.movd .xmm0 .eax).exec s).xmm .xmm0 == 0xffffffff#128
#guard ((XOp.movd .xmm7 .edi).exec s).xmm .xmm7 == 0x100#128
-- SSE operations leave every scalar flag and general-purpose register intact.
#guard ((XOp.bin .aesenc .xmm0 .xmm1).exec s).gpr .eax == s.gpr .eax
#guard ((XOp.sha256rnds2 .xmm0 .xmm1).exec s).cf == s.cf
#guard ((XOp.pclmulqdq .xmm0 .xmm1 0).exec s).zf == s.zf
#guard ((XOp.movd .xmm0 .eax).exec s).sf == s.sf
#guard ((XOp.bin .pshufb .xmm0 .xmm2).exec s).of == s.of
-- An unaligned load succeeds if all 16 bytes remain readable.
#guard (exec (.movdquLoad .xmm7 { base := .edi, disp := 1 })
  { s with rd := [⟨0x100, 17⟩] }).isSome

/-! ## Printing and feature declarations -/
#guard printer.instr (.xop (.bin .movdqa .xmm1 .xmm2)) == ["movdqa xmm1, xmm2"]
#guard printer.instr (.xop (.bin .paddd .xmm3 .xmm4)) == ["paddd xmm3, xmm4"]
#guard printer.instr (.xop (.bin .pxor .xmm5 .xmm6)) == ["pxor xmm5, xmm6"]
#guard printer.instr (.xop (.bin .por .xmm7 .xmm0)) == ["por xmm7, xmm0"]
#guard printer.instr (.xop (.bin .punpckldq .xmm1 .xmm2)) == ["punpckldq xmm1, xmm2"]
#guard printer.instr (.xop (.bin .punpckhdq .xmm3 .xmm4)) == ["punpckhdq xmm3, xmm4"]
#guard printer.instr (.xop (.bin .punpcklqdq .xmm5 .xmm6)) == ["punpcklqdq xmm5, xmm6"]
#guard printer.instr (.xop (.bin .punpckhqdq .xmm0 .xmm7)) == ["punpckhqdq xmm0, xmm7"]
#guard printer.instr (.xop (.shift .pslld .xmm1 7)) == ["pslld xmm1, 7"]
#guard printer.instr (.xop (.shift .psrld .xmm2 25)) == ["psrld xmm2, 25"]
#guard printer.instr (.xop (.pshufd .xmm3 .xmm4 0x93)) == ["pshufd xmm3, xmm4, 147"]
#guard printer.instr (.xop (.bin .pshufb .xmm5 .xmm6)) == ["pshufb xmm5, xmm6"]
#guard printer.instr (.xop (.bin .sha256msg1 .xmm7 .xmm0)) == ["sha256msg1 xmm7, xmm0"]
#guard printer.instr (.xop (.bin .sha256msg2 .xmm1 .xmm2)) == ["sha256msg2 xmm1, xmm2"]
#guard printer.instr (.xop (.palignr .xmm3 .xmm4 4)) == ["palignr xmm3, xmm4, 4"]
#guard printer.instr (.xop (.sha256rnds2 .xmm5 .xmm6)) == ["sha256rnds2 xmm5, xmm6, xmm0"]
#guard printer.instr (.xop (.bin .pand .xmm0 .xmm1)) == ["pand xmm0, xmm1"]
#guard printer.instr (.xop (.bin .pandn .xmm2 .xmm3)) == ["pandn xmm2, xmm3"]
#guard printer.instr (.xop (.bin .aesenc .xmm0 .xmm1)) == ["aesenc xmm0, xmm1"]
#guard printer.instr (.xop (.bin .aesenclast .xmm2 .xmm3)) == ["aesenclast xmm2, xmm3"]
#guard printer.instr (.xop (.aeskeygenassist .xmm3 .xmm4 0x36)) == ["aeskeygenassist xmm3, xmm4, 54"]
#guard printer.instr (.xop (.pclmulqdq .xmm5 .xmm6 0x11)) == ["pclmulqdq xmm5, xmm6, 17"]
#guard printer.instr (.xop (.shift .psllq .xmm7 1)) == ["psllq xmm7, 1"]
#guard printer.instr (.xop (.shift .psrlq .xmm0 63)) == ["psrlq xmm0, 63"]
#guard printer.instr (.xop (.shift .pslldq .xmm1 8)) == ["pslldq xmm1, 8"]
#guard printer.instr (.xop (.shift .psrldq .xmm2 4)) == ["psrldq xmm2, 4"]

#guard printer.instr (.xop (.movd .xmm7 .esi)) == ["movd xmm7, esi"]
#guard printer.instr (.movdquLoad .xmm7 { base := .edi, disp := 16 }) ==
  ["movdqu xmm7, XMMWORD PTR [edi+16]"]
#guard printer.instr (.movdquStore { base := .esp, disp := 4 } .xmm7) ==
  ["movdqu XMMWORD PTR [esp+4], xmm7"]
#guard isa.requires (.xop (.bin .pshufb .xmm1 .xmm2)) == ["ssse3"]
#guard isa.requires (.xop (.palignr .xmm1 .xmm2 4)) == ["ssse3"]
#guard isa.requires (.xop (.bin .sha256msg1 .xmm1 .xmm2)) == ["sha"]
#guard isa.requires (.xop (.bin .sha256msg2 .xmm1 .xmm2)) == ["sha"]
#guard isa.requires (.xop (.sha256rnds2 .xmm1 .xmm2)) == ["sha"]
#guard isa.requires (.xop (.bin .aesenc .xmm1 .xmm2)) == ["aes"]
#guard isa.requires (.xop (.bin .aesenclast .xmm1 .xmm2)) == ["aes"]
#guard isa.requires (.xop (.aeskeygenassist .xmm1 .xmm2 1)) == ["aes"]
#guard isa.requires (.xop (.pclmulqdq .xmm1 .xmm2 0)) == ["pclmulqdq"]
#guard isa.requires (.xop (.movd .xmm1 .eax)) == []
#guard isa.requires (.xop (.pshufd .xmm1 .xmm2 0xff)) == []
#guard isa.requires (.movdquLoad .xmm1 { base := .esp }) == []
#guard !isa.writesSp (.xop (.movd .xmm1 .esp))
#guard !isa.writesSp (.movdquLoad .xmm1 { base := .esp })

end VG.Test.X86Sse
