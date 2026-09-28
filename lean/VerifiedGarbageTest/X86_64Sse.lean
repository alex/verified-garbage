import VerifiedGarbage.TCB.X86_64.Print

/-!
# Semantics tests for the x86-64 SSE instructions

Each expected value was computed on an x86-64 CPU, by the same instruction
through its intrinsic (`_mm_add_epi32`, `_mm_shuffle_epi32`,
`_mm_sha256rnds2_epu32`, `_mm_aesenc_si128`, `_mm_clmulepi64_si128`, …; the
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
/-- The `pshufb` mask that reverses the bytes of each doubleword. -/
def c : BitVec 128 := 0x0c0d0e0f08090a0b0405060700010203#128

/-- A state with `a` in `xmm0`, `b` in `xmm1` and `c` in `xmm2`, and 16 bytes `17 i + 3` at
address `0x100`, readable. -/
def s : State where
  gpr r := if r = .rdi then 0x100 else 0
  cf := none
  zf := none
  sf := none
  of := none
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
#guard bin .paddq == 0x89abcdee812345677edcba9788888888#128
#guard bin .pmuludq == 0x0091a2b380000000086a1c970b88d780#128
#guard bin .aesenc == 0xd8908bc5e4ae3f56c95bfb9bd0b4a271#128
#guard bin .aesenclast == 0x8379dc203b20bd85479d91b9b512a2b2#128
#guard bin .aesdec == 0xfafbac38e6a5c5c37f30df5470d1274c#128
#guard bin .aesdeclast == 0xf06c979e72fdc00a76f15e1d1e06d604#128
-- `aesimc` reads only its source.
#guard bin .aesimc == 0xffffffff41f7daecbe082513851bd147#128

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

-- The S-box (FIPS 197 §5.1.1: `{00} ↦ {63}`, `{53} ↦ {ed}`), and the inverse S-box
-- inverts it.
#guard aesSbox 0x00 == 0x63 && aesSbox 0x53 == 0xed
#guard (List.range 256).all fun i => aesInvSbox (aesSbox (BitVec.ofNat 8 i)) == BitVec.ofNat 8 i

-- `movq xmm0, rdi` zeroes the upper quadword.
#guard ((XOp.movq .xmm0 .rdi).exec s).xmm .xmm0 == 0x100#128

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
#guard ((exec (.movdquLoad .xmm2 { base := .rdi }) s).map (·.xmm .xmm2)) ==
  some 0x02f1e0cfbead9c8b7a69584736251403#128
#guard (exec (.movdquLoad .xmm2 { base := .rdi, disp := 1 }) s).isNone
#guard (exec (.movdquStore { base := .rdi } .xmm0) s).isNone
#guard ((exec (.movdquStore { base := .rdi, disp := 0x100 } .xmm0) s).map
  (·.mem.readW 0x200 128)) == some a
#guard (exec (.movdquStore { base := .rdi, disp := 0x101 } .xmm0) s).isNone

/-! ## MXCSR and `lfence`

The expected values are those of an x86-64 CPU: `stmxcsr` after `ldmxcsr` of
`0x1FBF` stores the bytes `bf 1f 00 00`, the initial MXCSR of a process is
`0x1F80`, `ldmxcsr` of `0xFFFF` succeeds, and `ldmxcsr` of `0x36251403`
(the doubleword at `0x100` here), `0x10000` or `0x80000000` raises #GP
(SIGSEGV). -/

/-- `s` with `v` in MXCSR. -/
def withMxcsr (v : BitVec 32) : State := { s with mxcsr := v }

#guard s.mxcsr == 0x1F80
#guard ((exec (.stmxcsr { base := .rdi, disp := 0x100 }) (withMxcsr 0x1FBF)).map
  fun s' => [s'.mem 0x200, s'.mem 0x201, s'.mem 0x202, s'.mem 0x203]) == some [0xbf, 0x1f, 0, 0]
#guard (exec (.stmxcsr { base := .rdi }) s).isNone
#guard (exec (.stmxcsr { base := .rdi, disp := 0x10d }) s).isNone
/-- `s` with `v` stored at `0x200`, from MXCSR. -/
def stored (v : BitVec 32) : State :=
  ((exec (.stmxcsr { base := .rdi, disp := 0x100 }) (withMxcsr v)).getD s)
#guard ((exec (.ldmxcsr { base := .rdi, disp := 0x100 }) (stored 0x1FBF)).map (·.mxcsr)) ==
  some 0x1FBF
#guard ((exec (.ldmxcsr { base := .rdi, disp := 0x100 }) (stored 0xFFFF)).map (·.mxcsr)) ==
  some 0xFFFF
#guard (exec (.ldmxcsr { base := .rdi }) s).isNone
#guard (exec (.ldmxcsr { base := .rdi, disp := 0x100 }) (stored 0x10000)).isNone
#guard (exec (.ldmxcsr { base := .rdi, disp := 0x100 }) (stored 0x80000000)).isNone
#guard (exec (.ldmxcsr { base := .rdi, disp := 0x10d }) s).isNone
#guard ((exec .lfence (withMxcsr 0x1FBF)).map (·.mxcsr)) == some 0x1FBF
#guard ((exec .lfence s).map (·.xmm .xmm0)) == some a

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
#guard printer.instr (.xop (.bin .pshufb .xmm5 .xmm6)) == ["pshufb xmm5, xmm6"]
#guard printer.instr (.xop (.bin .sha256msg1 .xmm7 .xmm8)) == ["sha256msg1 xmm7, xmm8"]
#guard printer.instr (.xop (.bin .sha256msg2 .xmm9 .xmm10)) == ["sha256msg2 xmm9, xmm10"]
#guard printer.instr (.xop (.palignr .xmm11 .xmm12 4)) == ["palignr xmm11, xmm12, 4"]
#guard printer.instr (.xop (.sha256rnds2 .xmm13 .xmm14)) == ["sha256rnds2 xmm13, xmm14, xmm0"]
#guard printer.instr (.xop (.movq .xmm15 .r9)) == ["movq xmm15, r9"]
#guard printer.instr (.xop (.bin .pand .xmm0 .xmm1)) == ["pand xmm0, xmm1"]
#guard printer.instr (.xop (.bin .pandn .xmm2 .xmm3)) == ["pandn xmm2, xmm3"]
#guard printer.instr (.xop (.bin .paddq .xmm4 .xmm5)) == ["paddq xmm4, xmm5"]
#guard printer.instr (.xop (.bin .pmuludq .xmm6 .xmm7)) == ["pmuludq xmm6, xmm7"]
#guard printer.instr (.xop (.bin .aesenc .xmm8 .xmm9)) == ["aesenc xmm8, xmm9"]
#guard printer.instr (.xop (.bin .aesenclast .xmm10 .xmm11)) == ["aesenclast xmm10, xmm11"]
#guard printer.instr (.xop (.bin .aesdec .xmm12 .xmm13)) == ["aesdec xmm12, xmm13"]
#guard printer.instr (.xop (.bin .aesdeclast .xmm14 .xmm15)) == ["aesdeclast xmm14, xmm15"]
#guard printer.instr (.xop (.bin .aesimc .xmm1 .xmm2)) == ["aesimc xmm1, xmm2"]
#guard printer.instr (.xop (.aeskeygenassist .xmm3 .xmm4 0x36)) == ["aeskeygenassist xmm3, xmm4, 54"]
#guard printer.instr (.xop (.pclmulqdq .xmm5 .xmm6 0x11)) == ["pclmulqdq xmm5, xmm6, 17"]
#guard printer.instr (.xop (.shift .psllq .xmm7 1)) == ["psllq xmm7, 1"]
#guard printer.instr (.xop (.shift .psrlq .xmm8 63)) == ["psrlq xmm8, 63"]
#guard printer.instr (.xop (.shift .pslldq .xmm9 8)) == ["pslldq xmm9, 8"]
#guard printer.instr (.xop (.shift .psrldq .xmm10 4)) == ["psrldq xmm10, 4"]
#guard printer.instr (.stmxcsr { base := .rsp, disp := 8 }) == ["stmxcsr DWORD PTR [rsp+8]"]
#guard printer.instr (.ldmxcsr { base := .rdi }) == ["ldmxcsr DWORD PTR [rdi]"]
#guard printer.instr .lfence == ["lfence"]

/-! ## Required features -/

-- SSE2 is in the x86-64 baseline.
#guard isa.requires (.xop (.pshufd .xmm3 .xmm4 0x93)) == []
#guard isa.requires (.xop (.movq .xmm1 .rax)) == []
#guard isa.requires (.movdquLoad .xmm0 { base := .rdi }) == []
#guard isa.requires (.xop (.bin .pshufb .xmm1 .xmm2)) == ["ssse3"]
#guard isa.requires (.xop (.palignr .xmm1 .xmm2 4)) == ["ssse3"]
#guard isa.requires (.xop (.bin .sha256msg1 .xmm1 .xmm2)) == ["sha"]
#guard isa.requires (.xop (.bin .sha256msg2 .xmm1 .xmm2)) == ["sha"]
#guard isa.requires (.xop (.sha256rnds2 .xmm1 .xmm2)) == ["sha"]
#guard [XBinOp.pand, .pandn, .paddq, .pmuludq].all fun op => isa.requires (.xop (.bin op .xmm1 .xmm2)) == []
#guard [XShiftOp.psllq, .psrlq, .pslldq, .psrldq].all fun op => isa.requires (.xop (.shift op .xmm1 1)) == []
#guard [XBinOp.aesenc, .aesenclast, .aesdec, .aesdeclast, .aesimc].all fun op =>
  isa.requires (.xop (.bin op .xmm1 .xmm2)) == ["aes"]
#guard isa.requires (.xop (.aeskeygenassist .xmm1 .xmm2 1)) == ["aes"]
#guard isa.requires (.xop (.pclmulqdq .xmm1 .xmm2 0)) == ["pclmulqdq"]
-- SSE (`ldmxcsr`, `stmxcsr`) and SSE2 (`lfence`) are in the x86-64 baseline.
#guard isa.requires (.stmxcsr { base := .rsp }) == []
#guard isa.requires (.ldmxcsr { base := .rsp }) == []
#guard isa.requires .lfence == []

end VG.Test.Sse
