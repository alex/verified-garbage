import VerifiedGarbage.TCB.X86_64.Print

/-!
# Semantics tests for the x86-64 AVX-512 instructions

Each expected value was computed on an x86-64 CPU with AVX-512F, by the same
instruction through its intrinsic (`_mm512_add_epi32`, `_mm512_rol_epi32`,
`_mm512_shuffle_i32x4`, …) or in inline assembly (what VEX-encoded and
legacy SSE instructions and `vzeroupper` leave in bits 511:256), and is
compared with the model's result on the same inputs.
-/

namespace VG.Test.Avx512

open X86_64

def A : BitVec 512 := 0x0badf00dfeedfacedeadbeef00c0ffee8899aabbccddeeff00112233445566770f1e2d3c4b5a6978c3d2e1f08796a5b489abcdef01234567fedcba9876543210#512
def B : BitVec 512 := 0x0f0f0f0ff0f0f0f05555aaaa3333ccccf0e1d2c3b4a5968713579bdf2468ace00123456789abcdefdeadbeefcafebabeffffffff800000007fffffff12345678#512

/-- A state with `A` and `B` in `zmm0` and `zmm1`, all ones in `zmm5`, and 64
bytes `A` at address `0x100`, readable. -/
def s : State where
  gpr r := if r = .rdi then 0x100 else 0
  cf := none
  zf := none
  sf := none
  of := none
  xmm r := if r = .xmm0 then A.extractLsb' 0 128 else if r = .xmm1 then B.extractLsb' 0 128
    else if r = .xmm5 then -1 else 0
  ymmHi r := if r = .xmm0 then A.extractLsb' 128 128 else if r = .xmm1 then B.extractLsb' 128 128
    else if r = .xmm5 then -1 else 0
  zmmHi r := if r = .xmm0 then A.extractLsb' 256 256 else if r = .xmm1 then B.extractLsb' 256 256
    else if r = .xmm5 then -1 else 0
  mem addr := if 0x100 ≤ addr.toNat ∧ addr.toNat < 0x140 then
    A.extractLsb' (8 * (addr.toNat - 0x100)) 8 else 0
  rd := [⟨0x100, 64⟩]
  wr := [⟨0x200, 64⟩]

#guard s.zmm .xmm0 == A && s.zmm .xmm1 == B && s.mem.readW 0x100 512 == A
#guard (List.range 4).all fun i => s.zlane .xmm0 i == A.extractLsb' (128 * i) 128

/-- `zmm5` after `op`. -/
def run (op : ZOp) : BitVec 512 := (op.exec s).zmm .xmm5

/-- `zmm5` after `op zmm5, zmm0, zmm1`. -/
def bin (op : ZBinOp) : BitVec 512 := run (.zbin op .xmm5 .xmm0 .xmm1)

#guard bin .vpaddd == 0x1abcff1cefdeebbe3403699933f4ccba797b7d7e818385861368be1268be1357104172a3d5063767a280a0df5295607289abcdee812345677edcba9788888888#512
#guard bin .vpxord == 0x04a2ff020e1d0a3e8bf8144533f3332278787878787878781346b9ec603dca970e3d685bc2f1a4971d7f5f1f4d681f0a76543210812345678123456764606468#512
#guard bin .vpunpckldq == 0x5555aaaadeadbeef3333cccc00c0ffee13579bdf001122332468ace044556677deadbeefc3d2e1f0cafebabe8796a5b47ffffffffedcba981234567876543210#512
#guard bin .vpunpckhdq == 0x0f0f0f0f0badf00df0f0f0f0feedfacef0e1d2c38899aabbb4a59687ccddeeff012345670f1e2d3c89abcdef4b5a6978ffffffff89abcdef8000000001234567#512
#guard bin .vpunpcklqdq == 0x5555aaaa3333ccccdeadbeef00c0ffee13579bdf2468ace00011223344556677deadbeefcafebabec3d2e1f08796a5b47fffffff12345678fedcba9876543210#512
#guard bin .vpunpckhqdq == 0x0f0f0f0ff0f0f0f00badf00dfeedfacef0e1d2c3b4a596878899aabbccddeeff0123456789abcdef0f1e2d3c4b5a6978ffffffff8000000089abcdef01234567#512

/-- `zmm5` after `vprold zmm5, zmm0, n`. -/
def rol (n : BitVec 8) : BitVec 512 := run (.vprold .xmm5 .xmm0 n)

#guard rol 7 == 0xd6f8068576fd677f56df77ef607ff7004cd55dc46ef77fe6089119802ab33ba28f169e07ad34bc25e970f861cb52da43d5e6f7c491a2b3806e5d4c7f2a19083b#512
#guard rol 16 == 0xf00d0badfacefeedbeefdeadffee00c0aabb8899eeffccdd22330011667744552d3c0f1e69784b5ae1f0c3d2a5b48796cdef89ab45670123ba98fedc32107654#512
#guard rol 0 == A
#guard rol 32 == A
#guard rol 45 == 0xbe01a175bf59dfddb7ddfbd51ffdc01835577113bddff99b24466002accee88ac5a781e34d2f096b5c3e187ad4b690f279bdf13568ace02497531fdb86420eca#512
#guard rol 255 == 0x85d6f8067f76fd67ef56df7700607ff7c44cd55de66ef77f80089119a22ab33b078f169e25ad34bc61e970f843cb52dac4d5e6f78091a2b37f6e5d4c3b2a1908#512

#guard run (.vpshufd .xmm5 .xmm0 0x93) == 0xfeedfacedeadbeef00c0ffee0badf00dccddeeff00112233445566778899aabb4b5a6978c3d2e1f08796a5b40f1e2d3c01234567fedcba987654321089abcdef#512

/-- `zmm5` after `vshufi32x4 zmm5, zmm0, zmm1, n`. -/
def shuf (n : BitVec 8) : BitVec 512 := run (.vshufi32x4 .xmm5 .xmm0 .xmm1 n)

#guard shuf 0x44 == 0x0123456789abcdefdeadbeefcafebabeffffffff800000007fffffff123456780f1e2d3c4b5a6978c3d2e1f08796a5b489abcdef01234567fedcba9876543210#512
#guard shuf 0xee == 0x0f0f0f0ff0f0f0f05555aaaa3333ccccf0e1d2c3b4a5968713579bdf2468ace00badf00dfeedfacedeadbeef00c0ffee8899aabbccddeeff0011223344556677#512
#guard shuf 0x88 == 0xf0e1d2c3b4a5968713579bdf2468ace0ffffffff800000007fffffff123456788899aabbccddeeff001122334455667789abcdef01234567fedcba9876543210#512
#guard shuf 0xdd == 0x0f0f0f0ff0f0f0f05555aaaa3333cccc0123456789abcdefdeadbeefcafebabe0badf00dfeedfacedeadbeef00c0ffee0f1e2d3c4b5a6978c3d2e1f08796a5b4#512
#guard shuf 0x1b == 0xffffffff800000007fffffff123456780123456789abcdefdeadbeefcafebabe8899aabbccddeeff00112233445566770badf00dfeedfacedeadbeef00c0ffee#512

-- The destination may be a source, and only the destination changes.
#guard ((ZOp.zbin .vpaddd .xmm0 .xmm0 .xmm1).exec s).zmm .xmm0 == bin .vpaddd
#guard ((ZOp.zbin .vpaddd .xmm5 .xmm0 .xmm1).exec s).zmm .xmm0 == A

/-! ## Bits 511:256 under the other vector instructions -/

/-- A state with `A` in `zmm5`. -/
def s5 : State := (ZOp.vpshufd .xmm5 .xmm0 0xe4).exec s

#guard s5.zmm .xmm5 == A

-- VEX-encoded instructions zero them (`vpaddd ymm5, ymm5, ymm5`).
#guard ((VOp.vbin .vpaddd .l256 .xmm5 .xmm5 .xmm5).exec s5).zmm .xmm5 == 0x1e3c5a7896b4d2f087a5c3e00f2d4b6813579bde02468acefdb97530eca86420#512
-- Legacy SSE instructions keep them (`paddd xmm5, xmm5`).
#guard ((XOp.bin .paddd .xmm5 .xmm5).exec s5).zmm .xmm5 == 0x0badf00dfeedfacedeadbeef00c0ffee8899aabbccddeeff00112233445566770f1e2d3c4b5a6978c3d2e1f08796a5b413579bde02468acefdb97530eca86420#512
-- `vzeroupper` zeroes bits 511:128.
#guard ((VOp.vzeroupper).exec s5).zmm .xmm5 == 0x89abcdef01234567fedcba9876543210#512

/-! ## Memory -/

#guard ((exec (.vmovdqu32Load .xmm5 { base := .rdi }) s).map (·.zmm .xmm5)) == some A
#guard (exec (.vmovdqu32Load .xmm5 { base := .rdi, disp := 1 }) s).isNone
#guard ((exec (.vbroadcasti32x4 .xmm5 { base := .rdi, disp := 16 }) s).map (·.zmm .xmm5)) ==
  some 0x0f1e2d3c4b5a6978c3d2e1f08796a5b40f1e2d3c4b5a6978c3d2e1f08796a5b40f1e2d3c4b5a6978c3d2e1f08796a5b40f1e2d3c4b5a6978c3d2e1f08796a5b4#512
#guard (exec (.vbroadcasti32x4 .xmm5 { base := .rdi, disp := 49 }) s).isNone
#guard ((exec (.vmovdqu32Store { base := .rdi, disp := 0x100 } .xmm1) s).map
  (·.mem.readW 0x200 512)) == some B
#guard (exec (.vmovdqu32Store { base := .rdi, disp := 0x101 } .xmm1) s).isNone

/-! ## Printing -/

#guard printer.instr (.zop (.zbin .vpaddd .xmm1 .xmm2 .xmm15)) == ["vpaddd zmm1, zmm2, zmm15"]
#guard printer.instr (.zop (.zbin .vpxord .xmm1 .xmm2 .xmm3)) == ["vpxord zmm1, zmm2, zmm3"]
#guard printer.instr (.zop (.zbin .vpunpckhqdq .xmm4 .xmm5 .xmm6)) == ["vpunpckhqdq zmm4, zmm5, zmm6"]
#guard printer.instr (.zop (.vprold .xmm7 .xmm8 12)) == ["vprold zmm7, zmm8, 12"]
#guard printer.instr (.zop (.vpshufd .xmm9 .xmm10 147)) == ["vpshufd zmm9, zmm10, 147"]
#guard printer.instr (.zop (.vshufi32x4 .xmm11 .xmm12 .xmm13 0x88)) ==
  ["vshufi32x4 zmm11, zmm12, zmm13, 136"]
#guard printer.instr (.vmovdqu32Load .xmm0 { base := .rsi, disp := 64 }) ==
  ["vmovdqu32 zmm0, ZMMWORD PTR [rsi+64]"]
#guard printer.instr (.vmovdqu32Store { base := .rcx } .xmm14) == ["vmovdqu32 ZMMWORD PTR [rcx], zmm14"]
#guard printer.instr (.vbroadcasti32x4 .xmm1 { base := .rdi, disp := 48 }) ==
  ["vbroadcasti32x4 zmm1, XMMWORD PTR [rdi+48]"]

/-! ## Required features -/

#guard isa.requires (.zop (.zbin .vpaddd .xmm0 .xmm1 .xmm2)) == ["avx512f"]
#guard isa.requires (.zop (.vprold .xmm0 .xmm1 7)) == ["avx512f"]
#guard isa.requires (.zop (.vpshufd .xmm0 .xmm1 0)) == ["avx512f"]
#guard isa.requires (.zop (.vshufi32x4 .xmm0 .xmm1 .xmm2 0)) == ["avx512f"]
#guard isa.requires (.vmovdqu32Load .xmm0 { base := .rdi }) == ["avx512f"]
#guard isa.requires (.vmovdqu32Store { base := .rdi } .xmm0) == ["avx512f"]
#guard isa.requires (.vbroadcasti32x4 .xmm0 { base := .rdi }) == ["avx512f"]

end VG.Test.Avx512
