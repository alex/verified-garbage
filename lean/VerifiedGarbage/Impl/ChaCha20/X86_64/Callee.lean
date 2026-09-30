import VerifiedGarbage.Impl.ChaCha20.X86_64.Avx2
import VerifiedGarbage.Impl.ChaCha20.X86_64.Avx512

/-!
# The implementations of `vg_chacha20_xor` on x86-64

A function that calls `vg_chacha20_xor` (ChaCha20-Poly1305's `seal` and
`open`) takes the implementation it calls, a `Callee`, and is emitted once
for each (`Generic/ChaCha20Xor/X86_64/`).
-/

namespace VG.Impl.ChaCha20.X86_64

open VG.X86_64

/-- An implementation of `vg_chacha20_xor` to call: its symbol and its code. -/
structure Callee where
  name : String
  code : Prog isa

def Callee.scalar : Callee := ⟨"vg_chacha20_xor", Xor.xor⟩
def Callee.avx2 : Callee := ⟨"vg_chacha20_xor_avx2", Avx2.xor⟩
def Callee.avx512 : Callee := ⟨"vg_chacha20_xor_avx512", Avx512.xor⟩

end VG.Impl.ChaCha20.X86_64
