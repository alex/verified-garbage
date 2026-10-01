import VerifiedGarbage.TCB.X86_64.Print

/-!
# Semantics tests for the x86-64 AVX, AVX2 and AVX512_IFMA (`ymm`) instructions

Each expected value was computed on an x86-64 CPU, by the same instruction
through its intrinsic (`_mm256_add_epi32`, `_mm256_permute2x128_si256`,
`_mm256_sllv_epi64`, …), and is compared with the model's result on the same
inputs (`vpermd` and `vpmovmskb` on a Xeon with AVX2 and AVX-512, through
`_mm256_permutevar8x32_epi32`, `_mm256_movemask_epi8` and
`_mm_movemask_epi8`). `VEX.128` results were widened with `_mm256_zextsi128_si256`, since
the instruction zeroes bits 255:128 of its destination.
-/

namespace VG.Test.Avx

open X86_64

def A : BitVec 256 := 0x0f1e2d3c4b5a69788796a5b4c3d2e1f089abcdef01234567fedcba9876543210#256
def B : BitVec 256 := 0x0123456789abcdefdeadbeefcafebabeffffffff800000007fffffff12345678#256
/-- Shift counts: doublewords 7, 31, 0, 1, 63, 0, 64, 0 (from bit 0). -/
def C : BitVec 256 := 0x0000000000000040000000000000003f00000001000000000000001f00000007#256
/-- Shift counts: quadwords 1, 13, 63, 64 (from bit 0). -/
def D : BitVec 256 := 0x0000000000000040000000000000003f000000000000000d0000000000000001#256

/-- A state with `A`, `B`, `C` and `D` in `ymm0`–`ymm3`, all ones in `ymm5`, and 32 bytes
`17 i + 3` at address `0x100`, readable. -/
def s : State where
  gpr r := if r = .rdi then 0x100 else if r = .rax then 0x0123456789abcdef else 0
  cf := none
  zf := none
  sf := none
  of := none
  xmm r := if r = .xmm0 then A.extractLsb' 0 128 else if r = .xmm1 then B.extractLsb' 0 128
    else if r = .xmm2 then C.extractLsb' 0 128 else if r = .xmm3 then D.extractLsb' 0 128
    else if r = .xmm5 then -1 else 0
  ymmHi r := if r = .xmm0 then A.extractLsb' 128 128 else if r = .xmm1 then B.extractLsb' 128 128
    else if r = .xmm2 then C.extractLsb' 128 128 else if r = .xmm3 then D.extractLsb' 128 128
    else if r = .xmm5 then -1 else 0
  mem addr := if 0x100 ≤ addr.toNat ∧ addr.toNat < 0x120 then
    BitVec.ofNat 8 (17 * (addr.toNat - 0x100) + 3) else 0
  rd := [⟨0x100, 32⟩]
  wr := [⟨0x200, 32⟩]

#guard s.ymm .xmm0 == A && s.ymm .xmm1 == B && s.ymm .xmm2 == C && s.ymm .xmm3 == D

/-- `ymm5` after `op`. -/
def run (op : VOp) : BitVec 256 := (op.exec s).ymm .xmm5

/-- `ymm5` after `op ymm5, ymm0, ymm1` (or its `VEX.128` form). -/
def bin (op : VBinOp) (len : VLen := .l256) : BitVec 256 := run (.vbin op len .xmm5 .xmm0 .xmm1)

#guard bin .vpaddd == 0x104172a3d5063767664464a38ed19cae89abcdee812345677edcba9788888888#256
#guard bin .vpaddd .l128 == 0x0000000000000000000000000000000089abcdee812345677edcba9788888888#256
#guard bin .vpaddq == 0x104172a3d5063767664464a48ed19cae89abcdee812345677edcba9788888888#256
#guard bin .vpxor == 0x0e3d685bc2f1a497593b1b5b092c5b4e76543210812345678123456764606468#256
#guard bin .vpor == 0x0f3f6d7fcbfbedffdfbfbfffcbfefbfeffffffff81234567ffffffff76747678#256
#guard bin .vpand == 0x01020524090a49688684a4a4c2d2a0b089abcdef000000007edcba9812141210#256
#guard bin .vpandn == 0x0021404380a1848758291a4b082c1a0e76543210800000000123456700204468#256
#guard bin .vpshufb == 0xe1c3a5870000000000000000000000000000000000101010890000005498dc67#256
#guard bin .vpmuludq == 0x2885f4736b058f089b47405c1acc10200091a2b380000000086a1c970b88d780#256
#guard bin .vpunpckldq == 0xdeadbeef8796a5b4cafebabec3d2e1f07ffffffffedcba981234567876543210#256
#guard bin .vpunpckhdq == 0x012345670f1e2d3c89abcdef4b5a6978ffffffff89abcdef8000000001234567#256
#guard bin .vpunpcklqdq == 0xdeadbeefcafebabe8796a5b4c3d2e1f07fffffff12345678fedcba9876543210#256
#guard bin .vpunpckhqdq == 0x0123456789abcdef0f1e2d3c4b5a6978ffffffff8000000089abcdef01234567#256
#guard bin .vpaddw == 0x104172a3d5053767664364a38ed09cae89aacdee812345677edbba9788888888#256
#guard bin .vpsubw == 0x0dfbe7d5c1af9b89a8e9e6c5f8d4273289accdf0812345677eddba996420db98#256
#guard bin .vpsubd == 0x0dfae7d5c1ae9b89a8e8e6c5f8d4273289abcdf0812345677edcba99641fdb98#256
#guard bin .vpmullw == 0x2f1a5f247f1e8f08b45e4b0cfe5c1020765532118000000001244568f110d780#256
#guard bin .vpmullw .l128 == 0x00000000000000000000000000000000765532118000000001244568f110d780#256
#guard bin .vpmulhw == 0x00110c43dd2beb5f0fac16f30c75082200000000ff6e0000ff6e0000086910e8#256
#guard bin .vpackssdw == 0x7fff8000800080007fff7fff80008000ffff80007fff7fff80007fff80007fff#256
#guard bin .vpunpcklwd == 0xdead8796beefa5b4cafec3d2babee1f07ffffedcffffba981234765456783210#256
#guard bin .vpunpckhwd == 0x01230f1e45672d3c89ab4b5acdef6978ffff89abffffcdef8000012300004567#256
#guard bin .vpsubq == 0x0dfae7d4c1ae9b89a8e8e6c4f8d4273289abcdef812345677edcba99641fdb98#256
#guard bin .vpsubq .l128 == 0x0000000000000000000000000000000089abcdef812345677edcba99641fdb98#256

/-! `vpmadd52luq` and `vpmadd52huq` (`_mm256_madd52lo_epu64`,
`_mm256_madd52hi_epu64`, and `_mm_…` for `.l128`, on an Emerald Rapids Xeon), into the all-ones `ymm5`
(so the sums wrap), into a source, and with sources of 52 ones (whose
product's low 52 bits are 1 and high 52 bits `2⁵² - 2`). -/

#guard run (.vpmadd52luq .l256 .xmm5 .xmm0 .xmm1) == 0x000502bf6b058f07000413041acc101f000e5d4c7fffffff000c71c70b88d77f#256
#guard run (.vpmadd52huq .l256 .xmm5 .xmm0 .xmm1) == 0x0002e5fa1f559cf30005b5f64142cb3e000bcdeea2b3cd5c000cba97b9263968#256
#guard run (.vpmadd52luq .l128 .xmm5 .xmm0 .xmm1) == 0x00000000000000000000000000000000000e5d4c7fffffff000c71c70b88d77f#256
#guard run (.vpmadd52huq .l128 .xmm5 .xmm0 .xmm1) == 0x00000000000000000000000000000000000bcdeea2b3cd5c000cba97b9263968#256
#guard run (.vpmadd52huq .l256 .xmm5 .xmm0 .xmm0) == 0x000c8fa967e94bab0002c2fbbb1f464c0008b5832bffd93c000a2064cfea3c4d#256
#guard ((VOp.vpmadd52luq .l256 .xmm0 .xmm0 .xmm1).exec s).ymm .xmm0 == 0x0f232ffbb65ff880879ab8b8de9ef21089ba2b3b81234567fee92c5f81dd0990#256
#guard ((VOp.vpmadd52huq .l256 .xmm1 .xmm0 .xmm1).exec s).ymm .xmm1 == 0x01262b61a9016ae3deb374e60c4185fd000bcdee22b3cd5d800cba96cb5a8fe1#256

/-- `s` with `2⁵² - 1` in every quadword of `ymm6`. -/
def s52 : State := (VOp.vpbroadcastq .l256 .xmm6 .xmm6).exec
  ((VOp.vmovq .xmm6 .rax).exec { s with gpr := fun _ => 0x000fffffffffffff })

#guard ((VOp.vpmadd52huq .l256 .xmm5 .xmm6 .xmm6).exec s52).ymm .xmm5 == 0x000ffffffffffffd000ffffffffffffd000ffffffffffffd000ffffffffffffd#256
#guard ((VOp.vpmadd52luq .l256 .xmm5 .xmm6 .xmm6).exec s52).ymm .xmm5 == 0

/-- `ymm5` after `op ymm5, ymm0, n`. -/
def shift (op : XShiftOp) (n : BitVec 8) : BitVec 256 := run (.vshift op .l256 .xmm5 .xmm0 n)

#guard shift .pslld 7 == 0x8f169e00ad34bc00cb52da00e970f800d5e6f78091a2b3806e5d4c002a190800#256
#guard shift .psrld 25 == 0x0000000700000025000000430000006100000044000000000000007f0000003b#256
#guard shift .psllq 13 == 0xc5a7896b4d2f0000d4b6987a5c3e000079bde02468ace00097530eca86420000#256
#guard shift .psrlq 13 == 0x000078f169e25ad300043cb52da61e9700044d5e6f78091a0007f6e5d4c3b2a1#256
#guard shift .pslldq 4 == 0x4b5a69788796a5b4c3d2e1f00000000001234567fedcba987654321000000000#256
#guard shift .psrldq 4 == 0x000000000f1e2d3c4b5a69788796a5b40000000089abcdef01234567fedcba98#256
#guard shift .psrldq 15 == 0x0000000000000000000000000000000f00000000000000000000000000000089#256
#guard shift .pslld 32 == 0
#guard shift .psraw 3 == 0x01e305a7096b0d2ff0f2f4b6f87afc3ef135f9bd002408acffdbf7530eca0642#256
#guard shift .psraw 16 == 0x0000000000000000ffffffffffffffffffffffff00000000ffffffff00000000#256
#guard shift .psrad 3 == 0x01e3c5a7096b4d2ff0f2d4b6f87a5c3ef13579bd002468acffdb97530eca8642#256
#guard shift .psrad 15 == 0x00001e3c000096b4ffff0f2dffff87a5ffff135700000246fffffdb90000eca8#256
#guard shift .psrad 32 == 0x0000000000000000ffffffffffffffffffffffff00000000ffffffff00000000#256
#guard shift .psllw 3 == 0x78f069e05ad04bc03cb02da01e900f804d586f7809182b38f6e0d4c0b2a09080#256
#guard shift .psllw 16 == 0
#guard shift .psrlw 3 == 0x01e305a7096b0d2f10f214b6187a1c3e113519bd002408ac1fdb17530eca0642#256
#guard shift .psrlw 15 == 0x0000000000000000000100010001000100010001000000000001000100000000#256

#guard run (.vpshufd .l256 .xmm5 .xmm0 0x93) == 0x4b5a69788796a5b4c3d2e1f00f1e2d3c01234567fedcba987654321089abcdef#256
#guard run (.vpalignr .l256 .xmm5 .xmm0 .xmm1 4) == 0xc3d2e1f00123456789abcdefdeadbeef76543210ffffffff800000007fffffff#256
#guard run (.vpalignr .l256 .xmm5 .xmm0 .xmm1 20) == 0x000000000f1e2d3c4b5a69788796a5b40000000089abcdef01234567fedcba98#256
#guard run (.vpblendd .l256 .xmm5 .xmm0 .xmm1 0xa5) == 0x012345674b5a6978deadbeefc3d2e1f089abcdef80000000fedcba9812345678#256
#guard run (.vpblendd .l128 .xmm5 .xmm0 .xmm1 0x05) == 0x0000000000000000000000000000000089abcdef80000000fedcba9812345678#256

#guard run (.vvar .vpsllvd .l256 .xmm5 .xmm0 .xmm2) == 0x0f1e2d3c000000008796a5b40000000013579bde01234567000000002a190800#256
#guard run (.vvar .vpsrlvd .l256 .xmm5 .xmm0 .xmm2) == 0x0f1e2d3c000000008796a5b40000000044d5e6f7012345670000000100eca864#256
#guard run (.vvar .vpsllvq .l256 .xmm5 .xmm0 .xmm3) == 0x0000000000000000000000000000000079bde02468ace000fdb97530eca86420#256
#guard run (.vvar .vpsrlvq .l256 .xmm5 .xmm0 .xmm3) == 0x0000000000000000000000000000000100044d5e6f78091a7f6e5d4c3b2a1908#256
#guard run (.vvar .vpsllvq .l256 .xmm5 .xmm0 .xmm2) == 0x0000000000000000000000000000000000000000000000000000000000000000#256

#guard run (.vpbroadcastd .l256 .xmm5 .xmm1) == 0x1234567812345678123456781234567812345678123456781234567812345678#256
#guard run (.vpbroadcastq .l256 .xmm5 .xmm1) == 0x7fffffff123456787fffffff123456787fffffff123456787fffffff12345678#256
#guard run (.vpbroadcastd .l128 .xmm5 .xmm1) == 0x0000000000000000000000000000000012345678123456781234567812345678#256

#guard run (.vpermq .xmm5 .xmm0 0x1b) == 0xfedcba987654321089abcdef012345678796a5b4c3d2e1f00f1e2d3c4b5a6978#256
#guard run (.vpermq .xmm5 .xmm0 0xd8) == 0x0f1e2d3c4b5a697889abcdef012345678796a5b4c3d2e1f0fedcba9876543210#256
-- `vpermd` (`_mm256_permutevar8x32_epi32(src, idx)`): the indices' bits
-- above 2 are ignored (`C`'s doublewords 31, 63 and 64, and `B`'s).
#guard run (.vpermd .xmm5 .xmm2 .xmm0) == 0x7654321076543210765432100f1e2d3cfedcba98765432100f1e2d3c0f1e2d3c#256
#guard run (.vpermd .xmm5 .xmm1 .xmm0) == 0x0f1e2d3c0f1e2d3c0f1e2d3c4b5a69780f1e2d3c765432100f1e2d3c76543210#256
#guard run (.vpermd .xmm5 .xmm0 .xmm1) == 0xcafebabe12345678cafebabe1234567801234567012345671234567812345678#256
-- The indices may be the source, and the destination either.
#guard run (.vpermd .xmm5 .xmm0 .xmm0) == 0xc3d2e1f076543210c3d2e1f0765432100f1e2d3c0f1e2d3c7654321076543210#256
#guard ((VOp.vpermd .xmm0 .xmm0 .xmm0).exec s).ymm .xmm0 == 0xc3d2e1f076543210c3d2e1f0765432100f1e2d3c0f1e2d3c7654321076543210#256
#guard ((VOp.vpermd .xmm2 .xmm2 .xmm0).exec s).ymm .xmm2 == 0x7654321076543210765432100f1e2d3cfedcba98765432100f1e2d3c0f1e2d3c#256
#guard run (.vperm2i128 .xmm5 .xmm0 .xmm1 0x21) == 0xffffffff800000007fffffff123456780f1e2d3c4b5a69788796a5b4c3d2e1f0#256
#guard run (.vperm2i128 .xmm5 .xmm0 .xmm1 0x03) == 0x89abcdef01234567fedcba98765432100123456789abcdefdeadbeefcafebabe#256
#guard run (.vperm2i128 .xmm5 .xmm0 .xmm1 0x88) == 0x0000000000000000000000000000000000000000000000000000000000000000#256
#guard run (.vperm2i128 .xmm5 .xmm0 .xmm1 0x12) == 0x0f1e2d3c4b5a69788796a5b4c3d2e1f0ffffffff800000007fffffff12345678#256
#guard run (.vinserti128 .xmm5 .xmm0 .xmm1 0) == 0x0f1e2d3c4b5a69788796a5b4c3d2e1f0ffffffff800000007fffffff12345678#256
#guard run (.vinserti128 .xmm5 .xmm0 .xmm1 1) == 0xffffffff800000007fffffff1234567889abcdef01234567fedcba9876543210#256
#guard run (.vextracti128 .xmm5 .xmm0 0) == 0x0000000000000000000000000000000089abcdef01234567fedcba9876543210#256
#guard run (.vextracti128 .xmm5 .xmm0 1) == 0x000000000000000000000000000000000f1e2d3c4b5a69788796a5b4c3d2e1f0#256

-- Moves.
#guard run (.vmovdqa .l256 .xmm5 .xmm0) == A
#guard run (.vmovdqa .l128 .xmm5 .xmm0) == (A.extractLsb' 0 128).setWidth 256
#guard run (.vmovq .xmm5 .rax) == 0x0123456789abcdef#256

-- The destination may be a source.
#guard ((VOp.vbin .vpaddd .l256 .xmm0 .xmm0 .xmm1).exec s).ymm .xmm0 == 0x104172a3d5063767664464a38ed19cae89abcdee812345677edcba9788888888#256

-- Only the destination changes.
#guard ((VOp.vbin .vpaddd .l256 .xmm5 .xmm0 .xmm1).exec s).ymm .xmm0 == A
#guard ((VOp.vbin .vpaddd .l128 .xmm5 .xmm0 .xmm1).exec s).ymm .xmm1 == B

-- `vzeroupper` zeroes bits 255:128 of every register and keeps bits 127:0.
#guard ((VOp.vzeroupper).exec s).ymm .xmm0 == (A.extractLsb' 0 128).setWidth 256
#guard ((VOp.vzeroupper).exec s).ymm .xmm5 == (-1 : BitVec 128).setWidth 256

-- Legacy SSE instructions leave bits 255:128 unmodified.
#guard ((XOp.bin .paddd .xmm5 .xmm1).exec s).ymmHi .xmm5 == -1

/-! ## `vpmovmskb`

`_mm256_movemask_epi8` and `_mm_movemask_epi8`; the instruction itself, on
a 64-bit register of all ones, leaves bits 63:32 zero. -/

/-- `rax` (which `s` holds `0x0123456789abcdef` in) after `vpmovmskb eax, r`. -/
def mask (len : VLen) (r : XReg) : Option (BitVec 64) := (exec (.vpmovmskb len .rax r) s).map (·.gpr .rax)

#guard mask .l256 .xmm0 == some 0x00fff0f0
#guard mask .l256 .xmm1 == some 0x0ffff870
#guard mask .l128 .xmm0 == some 0xf0f0
#guard mask .l128 .xmm1 == some 0xf870
#guard mask .l256 .xmm5 == some 0xffffffff
#guard mask .l128 .xmm5 == some 0xffff
#guard mask .l256 .xmm4 == some 0
-- Only the destination changes.
#guard (exec (.vpmovmskb .l256 .rcx .xmm0) s).map (fun t => (t.gpr .rax, t.gpr .rcx, t.ymm .xmm0, t.cf)) ==
  some (0x0123456789abcdef, 0x00fff0f0, A, none)

/-! ## Memory -/

/-- The 32 bytes at `0x100`. -/
def M : BitVec 256 := s.mem.readW 0x100 256

#guard ((exec (.vmovdquLoad .l256 .xmm5 { base := .rdi }) s).map (·.ymm .xmm5)) == some M
#guard ((exec (.vmovdquLoad .l128 .xmm5 { base := .rdi, disp := 16 }) s).map (·.ymm .xmm5)) ==
  some ((M.extractLsb' 128 128).setWidth 256)
#guard (exec (.vmovdquLoad .l256 .xmm5 { base := .rdi, disp := 1 }) s).isNone
#guard (exec (.vmovdquLoad .l128 .xmm5 { base := .rdi, disp := 17 }) s).isNone
#guard ((exec (.vbroadcasti128 .xmm5 { base := .rdi }) s).map (·.ymm .xmm5)) ==
  some (M.extractLsb' 0 128 ++ M.extractLsb' 0 128)
#guard (exec (.vbroadcasti128 .xmm5 { base := .rdi, disp := 17 }) s).isNone
#guard ((exec (.vmovdquStore .l256 { base := .rdi, disp := 0x100 } .xmm0) s).map
  (·.mem.readW 0x200 256)) == some A
#guard ((exec (.vmovdquStore .l128 { base := .rdi, disp := 0x110 } .xmm0) s).map
  (·.mem.readW 0x210 128)) == some (A.extractLsb' 0 128)
#guard (exec (.vmovdquStore .l256 { base := .rdi, disp := 0x101 } .xmm0) s).isNone
#guard (exec (.vmovdquStore .l128 { base := .rdi, disp := 0x111 } .xmm0) s).isNone

/-! ## Printing -/

#guard printer.instr (.vop (.vbin .vpaddd .l256 .xmm1 .xmm2 .xmm15)) == ["vpaddd ymm1, ymm2, ymm15"]
#guard printer.instr (.vop (.vbin .vpxor .l128 .xmm1 .xmm2 .xmm3)) == ["vpxor xmm1, xmm2, xmm3"]
#guard printer.instr (.vop (.vmovdqa .l256 .xmm4 .xmm5)) == ["vmovdqa ymm4, ymm5"]
#guard printer.instr (.vop (.vshift .psrlq .l256 .xmm6 .xmm7 13)) == ["vpsrlq ymm6, ymm7, 13"]
#guard printer.instr (.vop (.vshift .pslldq .l128 .xmm6 .xmm7 4)) == ["vpslldq xmm6, xmm7, 4"]
#guard printer.instr (.vop (.vshift .psraw .l256 .xmm6 .xmm7 15)) == ["vpsraw ymm6, ymm7, 15"]
#guard printer.instr (.vop (.vshift .psrad .l128 .xmm6 .xmm7 31)) == ["vpsrad xmm6, xmm7, 31"]
#guard printer.instr (.vop (.vbin .vpmulhw .l256 .xmm1 .xmm2 .xmm3)) == ["vpmulhw ymm1, ymm2, ymm3"]
#guard printer.instr (.vop (.vbin .vpsubq .l256 .xmm1 .xmm2 .xmm3)) == ["vpsubq ymm1, ymm2, ymm3"]
#guard printer.instr (.vop (.vpmadd52luq .l256 .xmm1 .xmm2 .xmm15)) == ["vpmadd52luq ymm1, ymm2, ymm15"]
#guard printer.instr (.vop (.vpmadd52huq .l128 .xmm1 .xmm2 .xmm3)) == ["vpmadd52huq xmm1, xmm2, xmm3"]
#guard printer.instr (.vop (.vbin .vpackssdw .l256 .xmm1 .xmm2 .xmm3)) ==
  ["vpackssdw ymm1, ymm2, ymm3"]
#guard printer.instr (.vop (.vpshufd .l256 .xmm8 .xmm9 147)) == ["vpshufd ymm8, ymm9, 147"]
#guard printer.instr (.vop (.vpalignr .l256 .xmm10 .xmm11 .xmm12 8)) ==
  ["vpalignr ymm10, ymm11, ymm12, 8"]
#guard printer.instr (.vop (.vpblendd .l256 .xmm13 .xmm14 .xmm15 0xa5)) ==
  ["vpblendd ymm13, ymm14, ymm15, 165"]
#guard printer.instr (.vop (.vvar .vpsllvq .l256 .xmm0 .xmm1 .xmm2)) == ["vpsllvq ymm0, ymm1, ymm2"]
#guard printer.instr (.vop (.vvar .vpsrlvd .l128 .xmm0 .xmm1 .xmm2)) == ["vpsrlvd xmm0, xmm1, xmm2"]
#guard printer.instr (.vop (.vpbroadcastd .l256 .xmm3 .xmm4)) == ["vpbroadcastd ymm3, xmm4"]
#guard printer.instr (.vop (.vpbroadcastq .l128 .xmm3 .xmm4)) == ["vpbroadcastq xmm3, xmm4"]
#guard printer.instr (.vop (.vpermq .xmm5 .xmm6 0x1b)) == ["vpermq ymm5, ymm6, 27"]
#guard printer.instr (.vop (.vpermd .xmm5 .xmm6 .xmm15)) == ["vpermd ymm5, ymm6, ymm15"]
#guard printer.instr (.vpmovmskb .l256 .r9 .xmm3) == ["vpmovmskb r9d, ymm3"]
#guard printer.instr (.vpmovmskb .l128 .rax .xmm12) == ["vpmovmskb eax, xmm12"]
#guard printer.instr (.vop (.vperm2i128 .xmm7 .xmm8 .xmm9 0x21)) == ["vperm2i128 ymm7, ymm8, ymm9, 33"]
#guard printer.instr (.vop (.vinserti128 .xmm10 .xmm11 .xmm12 1)) ==
  ["vinserti128 ymm10, ymm11, xmm12, 1"]
#guard printer.instr (.vop (.vextracti128 .xmm13 .xmm14 1)) == ["vextracti128 xmm13, ymm14, 1"]
#guard printer.instr (.vop (.vmovq .xmm15 .r9)) == ["vmovq xmm15, r9"]
#guard printer.instr (.vop .vzeroupper) == ["vzeroupper"]
#guard printer.instr (.vmovdquLoad .l256 .xmm0 { base := .rdi, disp := 32 }) ==
  ["vmovdqu ymm0, YMMWORD PTR [rdi+32]"]
#guard printer.instr (.vmovdquLoad .l128 .xmm0 { base := .rdi }) == ["vmovdqu xmm0, XMMWORD PTR [rdi]"]
#guard printer.instr (.vmovdquStore .l256 { base := .rsi, index := some .rcx, scale := 8 } .xmm15) ==
  ["vmovdqu YMMWORD PTR [rsi+rcx*8], ymm15"]
#guard printer.instr (.vbroadcasti128 .xmm1 { base := .rdx }) ==
  ["vbroadcasti128 ymm1, XMMWORD PTR [rdx]"]

/-! ## Required features -/

#guard isa.requires (.vop (.vbin .vpaddd .l256 .xmm0 .xmm1 .xmm2)) == ["avx2"]
#guard isa.requires (.vop (.vbin .vpaddd .l128 .xmm0 .xmm1 .xmm2)) == ["avx"]
#guard isa.requires (.vop (.vshift .pslld .l256 .xmm0 .xmm1 1)) == ["avx2"]
#guard isa.requires (.vop (.vshift .pslld .l128 .xmm0 .xmm1 1)) == ["avx"]
#guard isa.requires (.vop (.vbin .vpmullw .l256 .xmm0 .xmm1 .xmm2)) == ["avx2"]
#guard isa.requires (.vop (.vbin .vpmullw .l128 .xmm0 .xmm1 .xmm2)) == ["avx"]
#guard isa.requires (.vop (.vbin .vpsubq .l256 .xmm0 .xmm1 .xmm2)) == ["avx2"]
#guard isa.requires (.vop (.vpmadd52luq .l256 .xmm0 .xmm1 .xmm2)) == ["avx512ifma", "avx512vl"]
#guard isa.requires (.vop (.vpmadd52huq .l128 .xmm0 .xmm1 .xmm2)) == ["avx512ifma", "avx512vl"]
#guard isa.requires (.vop (.vshift .psraw .l256 .xmm0 .xmm1 1)) == ["avx2"]
#guard isa.requires (.vop (.vpshufd .l256 .xmm0 .xmm1 1)) == ["avx2"]
#guard isa.requires (.vop (.vpalignr .l128 .xmm0 .xmm1 .xmm2 1)) == ["avx"]
#guard isa.requires (.vop (.vmovdqa .l256 .xmm0 .xmm1)) == ["avx"]
#guard isa.requires (.vop (.vmovq .xmm0 .rax)) == ["avx"]
#guard isa.requires (.vop .vzeroupper) == ["avx"]
#guard isa.requires (.vmovdquLoad .l256 .xmm0 { base := .rdi }) == ["avx"]
#guard isa.requires (.vmovdquStore .l128 { base := .rdi } .xmm0) == ["avx"]
#guard isa.requires (.vop (.vpblendd .l128 .xmm0 .xmm1 .xmm2 1)) == ["avx2"]
#guard isa.requires (.vop (.vvar .vpsllvq .l128 .xmm0 .xmm1 .xmm2)) == ["avx2"]
#guard isa.requires (.vop (.vpbroadcastd .l128 .xmm0 .xmm1)) == ["avx2"]
#guard isa.requires (.vop (.vpermq .xmm0 .xmm1 0)) == ["avx2"]
#guard isa.requires (.vop (.vperm2i128 .xmm0 .xmm1 .xmm2 0)) == ["avx2"]
#guard isa.requires (.vop (.vinserti128 .xmm0 .xmm1 .xmm2 0)) == ["avx2"]
#guard isa.requires (.vop (.vextracti128 .xmm0 .xmm1 0)) == ["avx2"]
#guard isa.requires (.vbroadcasti128 .xmm0 { base := .rdi }) == ["avx2"]
#guard isa.requires (.vop (.vpermd .xmm0 .xmm1 .xmm2)) == ["avx2"]
#guard isa.requires (.vpmovmskb .l256 .rax .xmm0) == ["avx2"]
#guard isa.requires (.vpmovmskb .l128 .rax .xmm0) == ["avx"]
#guard isa.writesSp (.vpmovmskb .l256 .rsp .xmm0)
#guard !isa.writesSp (.vpmovmskb .l256 .rax .xmm0)

end VG.Test.Avx
