import VerifiedGarbage.Impl.MlDsa.X86_64.Arith.Ntt
import VerifiedGarbage.Impl.MlDsa.X86_64.Arith.Mul
import VerifiedGarbage.Impl.MlDsa.X86_64.Arith.AddSub

/-!
# ML-DSA on x86-64: implementations of the polynomial arithmetic

Key generation, signing and verification call the polynomial arithmetic of
one implementation, a `Backend`: the code of `vg_mldsa_ntt`,
`vg_mldsa_inv_ntt`, `vg_mldsa_multiply_ntt`, `vg_mldsa_multiply_add_ntt`,
`vg_mldsa_add` and `vg_mldsa_sub`, whose names end with `sfx` (e.g.
`_avx2`; nothing for the SSE2 code, `sse2`). Each is a variant of the
interface `MlDsaArith` on x86-64 (`Variants/MlDsaArith/X86_64/`), and the
functions that call them are emitted once for each
(`Generic/MlDsaArith/X86_64/`).
-/

namespace VG.Impl.MlDsa.X86_64.Arith

open VG.X86_64

/-- An implementation of the polynomial arithmetic. -/
structure Backend where
  ntt : Prog isa
  invNtt : Prog isa
  mul : Prog isa
  mulAdd : Prog isa
  add : Prog isa
  sub : Prog isa
  /-- What the names of its functions, and of those calling them, end with. -/
  sfx : String

/-- The SSE2 code. -/
def Backend.sse2 : Backend := ⟨Arith.ntt, Arith.nttInv, Arith.mul, Arith.mulAdd, Arith.add, Arith.sub, ""⟩

/-- Every function empty, which the proofs that the functions calling a
backend never write `rsp` (and load MXCSR only to restore it) evaluate in
its place. -/
def Backend.empty : Backend := ⟨.block [], .block [], .block [], .block [], .block [], .block [], ""⟩

end VG.Impl.MlDsa.X86_64.Arith
