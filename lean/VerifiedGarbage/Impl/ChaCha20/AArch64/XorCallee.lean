import VerifiedGarbage.Impl.ChaCha20.AArch64.Xor
import VerifiedGarbage.Impl.ChaCha20.AArch64.Mixed8

namespace VG.Impl.ChaCha20.AArch64

open VG.AArch64

/-- A stream implementation called by ChaCha20-Poly1305. -/
structure XorCallee where
  name : String
  code : Prog isa
  suffix : String
  /-- Whether the eight-block kernel uses SVE2 (`Mixed8.xor true`), and so
  does ChaCha20-Poly1305's own copy of it (`Stitch.bulk`). -/
  sve : Bool := false

def XorCallee.scalar : XorCallee := ⟨"vg_chacha20_xor", Xor.xor, "", false⟩
def XorCallee.neon : XorCallee := ⟨"vg_chacha20_xor_neon", Mixed8.xor false, "_neon", false⟩
def XorCallee.sve2 : XorCallee := ⟨"vg_chacha20_xor_sve2", Mixed8.xor true, "_sve2", true⟩

end VG.Impl.ChaCha20.AArch64
