import VerifiedGarbageTest.X86_64Avx512

/-!
# Vector AES-GCM instruction tests

The expected 512-bit values concatenate four independent results computed
on an Intel Xeon E5-2696 v4 using the legacy 128-bit intrinsics
`_mm_aesenc_si128`, `_mm_aesenclast_si128`, `_mm_clmulepi64_si128`,
`_mm_shuffle_epi8`, `_mm_slli_si128` and `_mm_srli_si128`, on each lane of
`Avx512.A` and `Avx512.B`. This independently checks the lane-wise
transcription of the SDM; it does not claim hardware execution of the
256-bit or 512-bit instructions on that CPU.
-/

namespace VG.Test.VectorGcm

open X86_64

def s : State :=
  { Avx512.s with cf := some true, zf := some false, sf := some true, of := some false }

def aesRound : BitVec 512 := 0x8329ebae7abfb0d55133e88ee662770bf2fa88901859bfdbbd563acfe1c0f8bae971d5a642865f41f4055a99ec767364d8908bc5e4ae3f56c95bfb9bd0b4a271#512
def aesLast : BitVec 512 := 0xb49a19d8ed4a7c7b36c08775186662e4bb63e129d7593a9108b9b31ce0a93f15b296438ca73b1553c9df4763bc4042338379dc203b20bd85479d91b9b512a2b2#512

/-- Check all widths, destructive aliases of either source, upper-bit
clearing and preservation of other registers, flags and memory. -/
def checkV (op : XReg → VOp) (expected : BitVec 512) (len : VLen) : Bool :=
  [XReg.xmm5, .xmm0, .xmm1].all fun d =>
    let t := (op d).exec s
    t.zmm d == (expected.extractLsb' 0 (if len = .l128 then 128 else 256)).setWidth 512 &&
    [XReg.xmm0, .xmm1, .xmm5, .xmm15].all (fun r => r == d || t.zmm r == s.zmm r) &&
    [Reg.rdi, .rax, .rsp].all (fun r => t.gpr r == s.gpr r) &&
    t.cf == s.cf && t.zf == s.zf && t.sf == s.sf && t.of == s.of &&
    t.rd == s.rd && t.wr == s.wr && t.mem.readW 0x100 512 == Avx512.A

def checkZ (op : XReg → ZOp) (expected : BitVec 512) : Bool :=
  [XReg.xmm5, .xmm0, .xmm1].all fun d =>
    let t := (op d).exec s
    t.zmm d == expected &&
    [XReg.xmm0, .xmm1, .xmm5, .xmm15].all (fun r => r == d || t.zmm r == s.zmm r) &&
    [Reg.rdi, .rax, .rsp].all (fun r => t.gpr r == s.gpr r) &&
    t.cf == s.cf && t.zf == s.zf && t.sf == s.sf && t.of == s.of &&
    t.rd == s.rd && t.wr == s.wr && t.mem.readW 0x100 512 == Avx512.A

#guard [VLen.l128, .l256].all fun l =>
  checkV (fun d => .vbin .vaesenc l d .xmm0 .xmm1) aesRound l &&
  checkV (fun d => .vbin .vaesenclast l d .xmm0 .xmm1) aesLast l
#guard checkZ (fun d => .zbin .vaesenc d .xmm0 .xmm1) aesRound
#guard checkZ (fun d => .zbin .vaesenclast d .xmm0 .xmm1) aesLast

/-- The four quadword selections; unused imm8 bits must be ignored. -/
def products : List (BitVec 8 × BitVec 512) := [
  (0, 0x39dc3907f169b10a624566ef005a444800012461148e528d1c0e1a4c08816ca059caaf877df767669356cbf57ba7cfd82ada34c44d51ecf6d3aacfb2b4211780#512),
  (1, 0x0276c967330dbbafba22ca9912c021c809396d19078a458d153653341b857ba004e5eb032f1975bb9b2cda247c1c88503c4ca252f17b911ec53c5924080b6a68#512),
  (16, 0x04e8c50ab59f2b1b0a8841b1bbffafa0000fe1113bcbdad5101ff1012bdbcac500dadfd86f0eb00c20fafff84f2e902c55b469880716253416e608f800000000#512),
  (17, 0x006f411159cbee883a39d1c69c6281a07f878e896463956d6f979e997473857d000eef3c0fbae088202ecf1c2f9ac0a8789944a53cad9e8f80709e6e80000000#512)]

#guard products.all fun (n, expected) =>
  [VLen.l128, .l256].all (fun l =>
    checkV (fun d => .vpclmulqdq l d .xmm0 .xmm1 n) expected l &&
    checkV (fun d => .vpclmulqdq l d .xmm0 .xmm1 (n ||| 0xee)) expected l) &&
  checkZ (fun d => .vpclmulqdq d .xmm0 .xmm1 n) expected &&
  checkZ (fun d => .vpclmulqdq d .xmm0 .xmm1 (n ||| 0xee)) expected

#guard checkZ (fun d => .zbin .vpshufb d .xmm0 .xmm1) 0x0b0b0b0b00000000bebe00000000000000000000000000004400000033ff0000a587e1c30000000000000000000000000000000000101010890000005498dc67#512

/-! Byte shifts stay within 128-bit lanes, including boundary counts. -/
#guard checkZ (fun d => .vpslldq d .xmm0 0) Avx512.A
#guard checkZ (fun d => .vpslldq d .xmm0 1) 0xadf00dfeedfacedeadbeef00c0ffee0099aabbccddeeff0011223344556677001e2d3c4b5a6978c3d2e1f08796a5b400abcdef01234567fedcba987654321000#512
#guard checkZ (fun d => .vpslldq d .xmm0 8) 0xdeadbeef00c0ffee000000000000000000112233445566770000000000000000c3d2e1f08796a5b40000000000000000fedcba98765432100000000000000000#512
#guard checkZ (fun d => .vpslldq d .xmm0 15) 0xee00000000000000000000000000000077000000000000000000000000000000b400000000000000000000000000000010000000000000000000000000000000#512
#guard checkZ (fun d => .vpslldq d .xmm0 16) 0
#guard checkZ (fun d => .vpslldq d .xmm0 255) 0
#guard checkZ (fun d => .vpsrldq d .xmm0 0) Avx512.A
#guard checkZ (fun d => .vpsrldq d .xmm0 1) 0x000badf00dfeedfacedeadbeef00c0ff008899aabbccddeeff00112233445566000f1e2d3c4b5a6978c3d2e1f08796a50089abcdef01234567fedcba98765432#512
#guard checkZ (fun d => .vpsrldq d .xmm0 8) 0x00000000000000000badf00dfeedface00000000000000008899aabbccddeeff00000000000000000f1e2d3c4b5a6978000000000000000089abcdef01234567#512
#guard checkZ (fun d => .vpsrldq d .xmm0 15) 0x0000000000000000000000000000000b000000000000000000000000000000880000000000000000000000000000000f00000000000000000000000000000089#512
#guard checkZ (fun d => .vpsrldq d .xmm0 16) 0
#guard checkZ (fun d => .vpsrldq d .xmm0 255) 0

/-! Exact printed operands and CPU features for every new form. -/
#guard printer.instr (.vop (.vbin .vaesenc .l128 .xmm5 .xmm0 .xmm1)) == ["vaesenc xmm5, xmm0, xmm1"]
#guard isa.requires (.vop (.vbin .vaesenc .l128 .xmm5 .xmm0 .xmm1)) == ["aes", "avx"]
#guard !isa.writesSp (.vop (.vbin .vaesenc .l128 .xmm5 .xmm0 .xmm1))
#guard printer.instr (.vop (.vbin .vaesenc .l256 .xmm5 .xmm0 .xmm1)) == ["vaesenc ymm5, ymm0, ymm1"]
#guard isa.requires (.vop (.vbin .vaesenc .l256 .xmm5 .xmm0 .xmm1)) == ["vaes", "avx"]
#guard !isa.writesSp (.vop (.vbin .vaesenc .l256 .xmm5 .xmm0 .xmm1))
#guard printer.instr (.zop (.zbin .vaesenc .xmm5 .xmm0 .xmm1)) == ["vaesenc zmm5, zmm0, zmm1"]
#guard isa.requires (.zop (.zbin .vaesenc .xmm5 .xmm0 .xmm1)) == ["vaes", "avx512f"]
#guard !isa.writesSp (.zop (.zbin .vaesenc .xmm5 .xmm0 .xmm1))
#guard printer.instr (.vop (.vbin .vaesenclast .l128 .xmm5 .xmm0 .xmm1)) == ["vaesenclast xmm5, xmm0, xmm1"]
#guard isa.requires (.vop (.vbin .vaesenclast .l128 .xmm5 .xmm0 .xmm1)) == ["aes", "avx"]
#guard !isa.writesSp (.vop (.vbin .vaesenclast .l128 .xmm5 .xmm0 .xmm1))
#guard printer.instr (.vop (.vbin .vaesenclast .l256 .xmm5 .xmm0 .xmm1)) == ["vaesenclast ymm5, ymm0, ymm1"]
#guard isa.requires (.vop (.vbin .vaesenclast .l256 .xmm5 .xmm0 .xmm1)) == ["vaes", "avx"]
#guard !isa.writesSp (.vop (.vbin .vaesenclast .l256 .xmm5 .xmm0 .xmm1))
#guard printer.instr (.zop (.zbin .vaesenclast .xmm5 .xmm0 .xmm1)) == ["vaesenclast zmm5, zmm0, zmm1"]
#guard isa.requires (.zop (.zbin .vaesenclast .xmm5 .xmm0 .xmm1)) == ["vaes", "avx512f"]
#guard !isa.writesSp (.zop (.zbin .vaesenclast .xmm5 .xmm0 .xmm1))
#guard printer.instr (.vop (.vpclmulqdq .l128 .xmm5 .xmm0 .xmm1 17)) == ["vpclmulqdq xmm5, xmm0, xmm1, 17"]
#guard isa.requires (.vop (.vpclmulqdq .l128 .xmm5 .xmm0 .xmm1 17)) == ["pclmulqdq", "avx"]
#guard !isa.writesSp (.vop (.vpclmulqdq .l128 .xmm5 .xmm0 .xmm1 17))
#guard printer.instr (.vop (.vpclmulqdq .l256 .xmm5 .xmm0 .xmm1 17)) == ["vpclmulqdq ymm5, ymm0, ymm1, 17"]
#guard isa.requires (.vop (.vpclmulqdq .l256 .xmm5 .xmm0 .xmm1 17)) == ["vpclmulqdq", "avx"]
#guard !isa.writesSp (.vop (.vpclmulqdq .l256 .xmm5 .xmm0 .xmm1 17))
#guard printer.instr (.zop (.vpclmulqdq .xmm5 .xmm0 .xmm1 17)) == ["vpclmulqdq zmm5, zmm0, zmm1, 17"]
#guard isa.requires (.zop (.vpclmulqdq .xmm5 .xmm0 .xmm1 17)) == ["vpclmulqdq", "avx512f"]
#guard !isa.writesSp (.zop (.vpclmulqdq .xmm5 .xmm0 .xmm1 17))
#guard printer.instr (.zop (.zbin .vpshufb .xmm5 .xmm0 .xmm1)) == ["vpshufb zmm5, zmm0, zmm1"]
#guard isa.requires (.zop (.zbin .vpshufb .xmm5 .xmm0 .xmm1)) == ["avx512bw"]
#guard !isa.writesSp (.zop (.zbin .vpshufb .xmm5 .xmm0 .xmm1))
#guard printer.instr (.zop (.vpslldq .xmm5 .xmm0 8)) == ["vpslldq zmm5, zmm0, 8"]
#guard isa.requires (.zop (.vpslldq .xmm5 .xmm0 8)) == ["avx512bw"]
#guard !isa.writesSp (.zop (.vpslldq .xmm5 .xmm0 8))
#guard printer.instr (.zop (.vpsrldq .xmm5 .xmm0 8)) == ["vpsrldq zmm5, zmm0, 8"]
#guard isa.requires (.zop (.vpsrldq .xmm5 .xmm0 8)) == ["avx512bw"]
#guard !isa.writesSp (.zop (.vpsrldq .xmm5 .xmm0 8))

end VG.Test.VectorGcm
