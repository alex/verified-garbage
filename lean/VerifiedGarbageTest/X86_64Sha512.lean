import VerifiedGarbage.TCB.X86_64.Print

/-!
# Semantics tests for the x86-64 SHA512 extension

Each expected value was computed by the same instruction (`vsha512rnds2`,
`vsha512msg1`, `vsha512msg2`, in inline assembly) under Intel's Software
Development Emulator (SDE 10.13.1, `-arl`: Arrow Lake), since no CPU at hand
has the extension, and is compared with the model's result on the same
inputs. This tests the transcription of the SDM's pseudocode (which operand
holds which working variables, and which quadword is which, including when
the operands are the same register), which review of the TCB would
otherwise have to catch by eye. The same values were also checked against a
scalar SHA-512 reference (two rounds from `A, B, E, F` and `C, D, G, H`;
`W + σ₀` and `W + σ₁` of the message words).
-/

namespace VG.Test.Sha512Ext

open X86_64

def A : BitVec 256 := 0x0f1e2d3c4b5a69788796a5b4c3d2e1f089abcdef01234567fedcba9876543210#256
def B : BitVec 256 := 0x0123456789abcdefdeadbeefcafebabeffffffff800000007fffffff12345678#256
def C : BitVec 256 := 0xa54ff53a5f1d36f13c6ef372fe94f82bbb67ae8584caa73b6a09e667f3bcc908#256
def D : BitVec 256 := 0x5be0cd19137e21791f83d9abfb41bd6b9b05688c2b3e6c1f510e527fade682d1#256

/-- A state with `A`, `B`, `C` and `D` in `ymm0`–`ymm3`, and all ones in bits
511:256 of every register. -/
def s : State where
  gpr _ := 0
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

#guard run (.vsha512rnds2 .xmm0 .xmm1 .xmm2) .xmm0 == 0xc53bc204285a9ed3af9f087f442c0c27d76749654dbdffa1704106b42f85426e#256
#guard run (.vsha512rnds2 .xmm2 .xmm3 .xmm0) .xmm2 == 0x0e069d3a5d39a1886898bdb58575fb91facd88b5376459b2442870640e6a9af6#256
#guard run (.vsha512rnds2 .xmm3 .xmm2 .xmm1) .xmm3 == 0xdabb5c3b60f939b9c30baca77644c59e9a1a5321386430709276784d3384218f#256
#guard run (.vsha512rnds2 .xmm0 .xmm0 .xmm0) .xmm0 == 0xef7ae9aa570db266a88e3968b141438c85d3fefb2384b543411ff8d5277e5733#256
#guard run (.vsha512msg1 .xmm0 .xmm1) .xmm0 == 0x569e2d3bd386e13e0734da9e2543bbf73befb723bdd04d41a12bd53a27e6f98c#256
#guard run (.vsha512msg1 .xmm2 .xmm3) .xmm2 == 0x1ec43103b522a1e05eb71df56004b44e70db79326d1468585188661940a4d57c#256
#guard run (.vsha512msg1 .xmm1 .xmm1) .xmm1 == 0x48a3456711d845b54e40866c374dd55fd03529b455205e90fefffffed2b45678#256
#guard run (.vsha512msg2 .xmm0 .xmm1) .xmm0 == 0x4e6bca20429266c288f75bcb66db1a03fa4f13fcbcf776e1201d54e8d5580853#256
#guard run (.vsha512msg2 .xmm2 .xmm3) .xmm2 == 0x867eb074e235dd532181ac852033af7fd5ae6f066aea785b35d7883102925bcd#256
#guard run (.vsha512msg2 .xmm3 .xmm3) .xmm3 == 0xcaf45b7e4f13549b83a1e7bbb4dd08dcb54c290d115e3d3f1cdbf448bcbc1596#256

-- The destination's bits 511:256 are zeroed; no other register changes.
#guard ((VOp.vsha512rnds2 .xmm0 .xmm1 .xmm2).exec s).zmmHi .xmm0 == 0
#guard ((VOp.vsha512msg1 .xmm2 .xmm3).exec s).zmmHi .xmm2 == 0
#guard ((VOp.vsha512msg2 .xmm3 .xmm3).exec s).zmmHi .xmm3 == 0
#guard ((VOp.vsha512rnds2 .xmm0 .xmm1 .xmm2).exec s).zmmHi .xmm1 == -1
#guard run (.vsha512rnds2 .xmm0 .xmm1 .xmm2) .xmm1 == B && run (.vsha512rnds2 .xmm0 .xmm1 .xmm2) .xmm2 == C
#guard run (.vsha512msg1 .xmm0 .xmm1) .xmm1 == B && run (.vsha512msg2 .xmm0 .xmm1) .xmm1 == B

/-! ## Printing and CPU features -/

#guard printer.instr (.vop (.vsha512rnds2 .xmm1 .xmm2 .xmm3)) == ["vsha512rnds2 ymm1, ymm2, xmm3"]
#guard printer.instr (.vop (.vsha512msg1 .xmm4 .xmm5)) == ["vsha512msg1 ymm4, xmm5"]
#guard printer.instr (.vop (.vsha512msg2 .xmm14 .xmm15)) == ["vsha512msg2 ymm14, ymm15"]

-- The SDM's "CPUID Feature Flag" of each is SHA512.
#guard isa.requires (.vop (.vsha512rnds2 .xmm1 .xmm2 .xmm3)) == ["sha512"]
#guard isa.requires (.vop (.vsha512msg1 .xmm4 .xmm5)) == ["sha512"]
#guard isa.requires (.vop (.vsha512msg2 .xmm14 .xmm15)) == ["sha512"]

end VG.Test.Sha512Ext
