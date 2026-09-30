import VerifiedGarbage.Impl.MlDsa.Arm.Sample.Common
import VerifiedGarbage.Impl.MlDsa.Arm.Pack.Encode

/-!
# ML-DSA on 32-bit ARM: `vg_mldsa_expand_mask_poly`

`expandMask(seed = r0, gamma1 = r1, a = r2, scratch = r3)` (see
`Common.lean` for the layout) squeezes 640 bytes of SHAKE256 of the 66 bytes
of the seed (5 blocks, which also hold the 576 bytes that `γ₁ = 2¹⁷` needs),
and unpacks the first `32c` of them, `c = 18` or `20` (chosen by a branch
on the public `γ₁`), with the loop of `vg_mldsa_bit_unpack` for
`(a, b) = (γ₁ - 1, γ₁)` (`Pack.unpackLoop (Pack.buFin γ₁)`): coefficient
`i` is `γ₁` minus the `c`-bit field `i`, modulo `q`. There is no branch on
the data, and the addresses depend only on the pointers and `γ₁`: it is
constant time.
-/

namespace VG.Impl.MlDsa.Arm.Sample

open VG.Arm
open VG.Impl.MlDsa.Arm.Pack (unpackLoop buFin)

/-- The fields, from the XOF output at `scratch + 840` to `a`. -/
def emLoop (c : Nat) : Prog isa :=
  .seq (.block [.dp .add .r0 .r6 (.imm 840), .mov .r1 (.reg .r5)])
    (if c = 18 then unpackLoop (buFin 131072) 18 4 9 else unpackLoop (buFin 524288) 20 2 5)

def expandMask : Prog isa :=
  .seq (.block (pro .r3 .r2 (.reg .r1) (.imm 66) .r0))
    (.seq (sponge 136 640)
      (.seq (.seq (.block [.cmp .r7 (.imm 0x20000)]) (.ite .eq (emLoop 18) (emLoop 20)))
        (.block epi)))

end VG.Impl.MlDsa.Arm.Sample
