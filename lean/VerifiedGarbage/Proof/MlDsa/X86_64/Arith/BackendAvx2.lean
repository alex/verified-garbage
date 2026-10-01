import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.Backend
import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.YNtt
import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.YMul
import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.YAddSub
import VerifiedGarbage.Proof.MlDsa.X86_64.Round.YBits

/-!
# ML-DSA on x86-64: the polynomial arithmetic with AVX2, as an `ArithImpl`

Untrusted: everything here is checked by Lean. The AVX2 code
(`Impl/MlDsa/X86_64/Arith/Avx2.lean`) meets what the callers of the
polynomial arithmetic need of it (`FnOk`), and requires AVX and AVX2.
-/

namespace VG.Proof.MlDsa.X86_64

open VG VG.X86_64 VG.Impl.MlDsa.X86_64.Arith

/-- The AVX2 code. -/
def ArithImpl.avx2 : ArithImpl where
  code := .avx2
  ok :=
    { ntt := FnOk.of Arith.nttY_verified (by decide +kernel) (by decide +kernel) (by decide +kernel)
        (by decide +kernel)
      invNtt := FnOk.of Arith.nttInvY_verified (by decide +kernel) (by decide +kernel) (by decide +kernel)
        (by decide +kernel)
      mul := FnOk.of Arith.mulY_verified (by decide +kernel) (by decide +kernel) (by decide +kernel)
        (by decide +kernel)
      mulAdd := FnOk.of Arith.mulAddY_verified (by decide +kernel) (by decide +kernel) (by decide +kernel)
        (by decide +kernel)
      add := FnOk.of Arith.addY_verified (by decide +kernel) (by decide +kernel) (by decide +kernel)
        (by decide +kernel)
      sub := FnOk.of Arith.subY_verified (by decide +kernel) (by decide +kernel) (by decide +kernel)
        (by decide +kernel)
      highBits := FnOk.of Round.highBitsY_verified (by decide +kernel) (by decide +kernel) (by decide +kernel)
        (by decide +kernel)
      lowBits := FnOk.of Round.lowBitsY_verified (by decide +kernel) (by decide +kernel) (by decide +kernel)
        (by decide +kernel) }
  features := ["avx", "avx2"]

end VG.Proof.MlDsa.X86_64
