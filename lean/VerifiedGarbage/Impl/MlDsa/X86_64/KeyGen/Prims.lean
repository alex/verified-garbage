import VerifiedGarbage.Impl.MlKem.X86_64.Frag

/-!
# ML-DSA on x86-64: the primitives key generation calls

`vg_mldsa*_keygen` is a sequence of calls of ML-DSA's polynomial
primitives (`Spec/MlDsa/Poly.lean`) and of the SHA-3 sponge functions. Its
code is written for any implementations of the primitives, given as a
`Prims`: the code of each primitive it calls, which it calls by the name of
the artifact that has that code.
-/

namespace VG.Impl.MlDsa.X86_64.KeyGen

open VG.X86_64

/-- The code of the primitives key generation calls. -/
structure Prims where
  /-- `vg_mldsa_ntt` -/
  ntt : Prog isa
  /-- `vg_mldsa_inv_ntt` -/
  invNtt : Prog isa
  /-- `vg_mldsa_multiply_ntt` -/
  mul : Prog isa
  /-- `vg_mldsa_multiply_add_ntt` -/
  mulAdd : Prog isa
  /-- `vg_mldsa_add` -/
  add : Prog isa
  /-- `vg_mldsa_rej_ntt_poly` -/
  rejNtt : Prog isa
  /-- `vg_mldsa_rej_bounded_poly` -/
  rejBounded : Prog isa
  /-- `vg_mldsa_power2round` -/
  power2Round : Prog isa
  /-- `vg_mldsa_simple_bit_pack` -/
  simpleBitPack : Prog isa
  /-- `vg_mldsa_bit_pack` -/
  bitPack : Prog isa
  /-- `vg_mldsa_rej_ntt_poly4` -/
  rej4 : Prog isa
  /-- What the names of the polynomial arithmetic's functions end with (`Arith.Backend`). -/
  sfx : String := ""

end VG.Impl.MlDsa.X86_64.KeyGen
