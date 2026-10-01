import VerifiedGarbage.Impl.ChaCha20.AArch64.Xor
import VerifiedGarbage.Impl.ChaCha20.AArch64.Mixed5

namespace VG.Impl.ChaCha20.AArch64

open VG.AArch64

/-- A stream implementation called by ChaCha20-Poly1305. -/
structure XorCallee where
  name : String
  code : Prog isa
  suffix : String

def XorCallee.scalar : XorCallee := ⟨"vg_chacha20_xor", Xor.xor, ""⟩
def XorCallee.neon : XorCallee := ⟨"vg_chacha20_xor_neon", Mixed5.xor, "_neon"⟩

end VG.Impl.ChaCha20.AArch64
