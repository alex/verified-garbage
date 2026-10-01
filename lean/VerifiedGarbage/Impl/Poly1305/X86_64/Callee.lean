import VerifiedGarbage.Impl.Poly1305.X86_64.Avx512

/-!
# The implementations of `vg_poly1305_blocks` on x86-64

A function that calls `vg_poly1305_blocks` (ChaCha20-Poly1305's `seal` and
`open`) takes the implementation it calls, a `Blocks`. Unlike
`ChaCha20.X86_64.Callee`, this is the list of implementations itself, so
that a proof can evaluate the code of the one called (the constant-time
check of `seal` and `open` descends into their calls).
-/

namespace VG.Impl.Poly1305.X86_64

open VG.X86_64

/-- An implementation of `vg_poly1305_blocks` to call. -/
inductive Blocks where
  /-- `vg_poly1305_blocks`, in the baseline ISA. -/
  | scalar
  /-- `vg_poly1305_blocks_avx2`. -/
  | avx2
  /-- `vg_poly1305_blocks_avx512`. -/
  | avx512

/-- Its symbol. -/
def Blocks.name : Blocks → String
  | .scalar => "vg_poly1305_blocks"
  | .avx2 => "vg_poly1305_blocks_avx2"
  | .avx512 => "vg_poly1305_blocks_avx512"

/-- Its code. -/
def Blocks.code : Blocks → Prog isa
  | .scalar => blocks
  | .avx2 => Avx2.blocksAvx2
  | .avx512 => Avx512.blocksAvx512

/-- The CPU features its code requires. -/
def Blocks.features : Blocks → List String
  | .scalar => []
  | .avx2 => ["avx", "avx2"]
  | .avx512 => ["avx", "avx512f", "avx2"]

end VG.Impl.Poly1305.X86_64
