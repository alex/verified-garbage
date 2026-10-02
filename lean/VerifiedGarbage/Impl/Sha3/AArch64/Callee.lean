import VerifiedGarbage.Impl.Sha3.AArch64

namespace VG.Impl.Sha3.AArch64

/-- A permutation implementation and the suffix propagated to every caller. -/
structure Callee where
  name : String
  code : Prog VG.AArch64.isa
  suffix : String
  /-- Paired-state sponge kernels may use ARM SHA3 instructions on this backend. -/
  pairedSha3 : Bool := false
  /-- An independently verified full absorb entry point, when this backend
  keeps the permutation state resident across complete input blocks. -/
  absorbOverride : Option (Prog VG.AArch64.isa) := none

def Callee.scalar : Callee where
  name := "vg_keccak_f1600"
  code := permute
  suffix := ""

end VG.Impl.Sha3.AArch64
