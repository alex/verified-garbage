import VerifiedGarbage.Impl.CmacAes.AArch64

namespace VG.Impl.CmacAes.AArch64
open VG.AArch64
/-- A whole-block CMAC chaining implementation for streaming callers. -/
structure Update where
  name : String
  code : Prog isa
end VG.Impl.CmacAes.AArch64
