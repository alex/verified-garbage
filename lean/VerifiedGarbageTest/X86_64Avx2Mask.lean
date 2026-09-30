import VerifiedGarbage.TCB.X86_64.Print

/-!
# Semantics tests for x86-64 PCMPGTD, VPCMPGTD, VPERMD, VPMOVZXBD and VMOVMSKPS

Each expected value was computed by the same instruction on an x86-64 CPU
with AVX2 (through the Rust intrinsics `_mm_cmpgt_epi32`,
`_mm256_cmpgt_epi32`, `_mm256_permutevar8x32_epi32`, `_mm256_cvtepu8_epi32`
and `_mm256_movemask_ps`, which compile to these instructions), and is
compared with the model's result on the same inputs. This tests the
transcription of the SDM's pseudocode: the signed comparison and which
operand is compared with which, which operand of VPERMD holds the indices,
which bytes VPMOVZXBD extends, and the order of the bits of VMOVMSKPS.
-/

namespace VG.Test.Avx2Mask

open X86_64

def A : BitVec 256 := 0x0f1e2d3c4b5a69788796a5b4c3d2e1f089abcdef01234567fedcba9876543210#256
def B : BitVec 256 := 0x0123456789abcdefdeadbeefcafebabeffffffff800000007fffffff12345678#256
def C : BitVec 256 := 0xa54ff53a5f1d36f13c6ef372fe94f82bbb67ae8584caa73b6a09e667f3bcc908#256
def D : BitVec 256 := 0x5be0cd19137e21791f83d9abfb41bd6b9b05688c2b3e6c1f510e527fade682d1#256

/-- A state with `A`, `B`, `C` and `D` in `ymm0`–`ymm3`, all ones in bits
511:256 of every register and in every general-purpose register. -/
def s : State where
  gpr _ := -1
  cf := none
  zf := none
  sf := none
  of := none
  xmm r := if r = .xmm0 then A.extractLsb' 0 128 else if r = .xmm1 then B.extractLsb' 0 128
    else if r = .xmm2 then C.extractLsb' 0 128 else if r = .xmm3 then D.extractLsb' 0 128 else 0
  ymmHi r := if r = .xmm0 then A.extractLsb' 128 128 else if r = .xmm1 then B.extractLsb' 128 128
    else if r = .xmm2 then C.extractLsb' 128 128 else if r = .xmm3 then D.extractLsb' 128 128 else 0
  zmmHi _ := -1
  mem _ := 0
  rd := []
  wr := []

#guard s.ymm .xmm0 == A && s.ymm .xmm1 == B && s.ymm .xmm2 == C && s.ymm .xmm3 == D

/-- Register `d` after `op`. -/
def run (op : VOp) (d : XReg) : BitVec 256 := (op.exec s).ymm d

/-! ## VPCMPGTD and PCMPGTD: `SRC1 > SRC2`, signed -/

#guard run (.vbin .vpcmpgtd .l256 .xmm4 .xmm0 .xmm1) .xmm4 ==
  0xffffffffffffffff000000000000000000000000ffffffff00000000ffffffff#256
#guard run (.vbin .vpcmpgtd .l256 .xmm4 .xmm1 .xmm0) .xmm4 ==
  0x0000000000000000ffffffffffffffffffffffff00000000ffffffff00000000#256
#guard run (.vbin .vpcmpgtd .l256 .xmm2 .xmm2 .xmm3) .xmm2 ==
  0x00000000ffffffffffffffffffffffffffffffff00000000ffffffffffffffff#256
#guard run (.vbin .vpcmpgtd .l256 .xmm0 .xmm0 .xmm0) .xmm0 == 0
-- The legacy SSE form compares `DEST` with `SRC` and leaves bits 511:128.
#guard ((XOp.bin .pcmpgtd .xmm0 .xmm1).exec s).xmm .xmm0 == 0x00000000ffffffff00000000ffffffff#128
#guard ((XOp.bin .pcmpgtd .xmm3 .xmm2).exec s).xmm .xmm3 == 0x00000000ffffffff0000000000000000#128
#guard ((XOp.bin .pcmpgtd .xmm0 .xmm1).exec s).ymmHi .xmm0 == A.extractLsb' 128 128

/-! ## VPERMD: the doublewords of `src` at the indices in `idx` -/

#guard run (.vpermd .xmm4 .xmm0 .xmm1) .xmm4 ==
  0xcafebabe12345678cafebabe1234567801234567012345671234567812345678#256
#guard run (.vpermd .xmm4 .xmm2 .xmm3) .xmm4 ==
  0x2b3e6c1f510e527f2b3e6c1f9b05688c1f83d9ab9b05688c5be0cd19ade682d1#256
#guard run (.vpermd .xmm1 .xmm1 .xmm1) .xmm1 ==
  0x01234567012345670123456789abcdef01234567123456780123456712345678#256

/-! ## VPMOVZXBD: the low eight bytes, zero-extended -/

#guard run (.vpmovzxbd .xmm4 .xmm0) .xmm4 ==
  0x000000fe000000dc000000ba0000009800000076000000540000003200000010#256
#guard run (.vpmovzxbd .xmm2 .xmm2) .xmm2 ==
  0x0000006a00000009000000e600000067000000f3000000bc000000c900000008#256

-- The destination's bits 511:256 are zeroed; no other register changes.
#guard ((VOp.vpermd .xmm4 .xmm0 .xmm1).exec s).zmmHi .xmm4 == 0
#guard ((VOp.vpmovzxbd .xmm4 .xmm0).exec s).zmmHi .xmm4 == 0
#guard ((VOp.vbin .vpcmpgtd .l256 .xmm4 .xmm0 .xmm1).exec s).zmmHi .xmm4 == 0
#guard run (.vpermd .xmm4 .xmm0 .xmm1) .xmm0 == A && run (.vpermd .xmm4 .xmm0 .xmm1) .xmm1 == B
#guard ((VOp.vpermd .xmm4 .xmm0 .xmm1).exec s).zmmHi .xmm0 == -1

/-! ## VMOVMSKPS: the sign bits of the doublewords, zero-extended -/

/-- `r` after `vmovmskps r, x`. -/
def msk (r : Reg) (x : XReg) : Option (BitVec 64) := (exec (.vmovmskps r x) s).map (·.gpr r)

#guard msk .rax .xmm0 == some 58
#guard msk .rcx .xmm1 == some 124
#guard msk .r8 .xmm2 == some 157
#guard msk .r15 .xmm3 == some 25
-- No flag or other register changes.
#guard (exec (.vmovmskps .rax .xmm0) s).map (·.gpr .rcx) == some (-1)
#guard (exec (.vmovmskps .rax .xmm0) s).map (·.cf) == some none

/-! ## Printing and CPU features -/

#guard printer.instr (.xop (.bin .pcmpgtd .xmm1 .xmm2)) == ["pcmpgtd xmm1, xmm2"]
#guard printer.instr (.vop (.vbin .vpcmpgtd .l256 .xmm1 .xmm2 .xmm3)) == ["vpcmpgtd ymm1, ymm2, ymm3"]
#guard printer.instr (.vop (.vpermd .xmm1 .xmm2 .xmm3)) == ["vpermd ymm1, ymm2, ymm3"]
#guard printer.instr (.vop (.vpmovzxbd .xmm4 .xmm5)) == ["vpmovzxbd ymm4, xmm5"]
#guard printer.instr (.vmovmskps .rax .xmm15) == ["vmovmskps eax, ymm15"]

-- The SDM's "CPUID Feature Flag": SSE2 (in the baseline) for PCMPGTD, AVX2
-- for VPCMPGTD (VEX.256), VPERMD and VPMOVZXBD (VEX.256), AVX for VMOVMSKPS.
#guard isa.requires (.xop (.bin .pcmpgtd .xmm1 .xmm2)) == []
#guard isa.requires (.vop (.vbin .vpcmpgtd .l256 .xmm1 .xmm2 .xmm3)) == ["avx2"]
#guard isa.requires (.vop (.vpermd .xmm1 .xmm2 .xmm3)) == ["avx2"]
#guard isa.requires (.vop (.vpmovzxbd .xmm4 .xmm5)) == ["avx2"]
#guard isa.requires (.vmovmskps .rax .xmm15) == ["avx"]

end VG.Test.Avx2Mask
