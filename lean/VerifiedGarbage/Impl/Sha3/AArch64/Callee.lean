import VerifiedGarbage.Impl.Sha3.AArch64

namespace VG.Impl.Sha3.AArch64

/-- A permutation implementation and the suffix propagated to every caller. -/
structure Callee where
  name : String
  code : Prog VG.AArch64.isa
  suffix : String

def Callee.scalar : Callee := ⟨"vg_keccak_f1600", permute, ""⟩

end VG.Impl.Sha3.AArch64
