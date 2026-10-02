import VerifiedGarbage.TCB.X86_64.Target
import VerifiedGarbage.Proof.Ed25519.X86_64.ScalarBasePrecomputedVerified

/-! Complete unsigned scalar multiplication by the Ed25519 base point. -/

namespace VG.Artifacts.Ed25519ScalarBase.X86_64

def artifacts : List Artifact := [
  { Spec.Ed25519.scalarBaseApi with
    target := X86_64.target
    doc := Spec.Ed25519.scalarBaseApi.doc (notes := ["Uses baseline integer instructions \
      and a fixed schedule for all 256 input bits. Point tables and saved registers \
      reside in `scratch`."])
    code := Impl.Ed25519.X86_64.scalarBase Impl.X25519.X86_64.baseline
    contract := Spec.Ed25519.scalarBaseContract X86_64.abi
    verified := Proof.Ed25519.X86_64.scalarBase_verified (fld := Impl.X25519.X86_64.baseline)
    spSafe := Code.all_of_allInstrs (by lit_decide) },
  { Spec.Ed25519.scalarBaseApi with
    target := X86_64.target
    name := "vg_ed25519_scalar_base_precomputed"
    doc := Spec.Ed25519.scalarBaseApi.doc (notes := ["Uses baseline integer instructions and \
      a comb: 32 tables of the multiples [k 256^j]B (k ≤ 8) of the base point, precomputed as \
      [Y - X, Y + X, 2dT, 2Z] and checked against the specification in Lean. Each of the \
      scalar's 64 nibbles n gives the digit n - 8, whose magnitude selects its table entry in \
      constant time (every entry is read, masked) and whose sign negates it, or not, under a \
      mask; the odd digits are added first to [G]B (G = 8 Σ 256^j makes up for the offset), then \
      four doublings and [G]B again, then the even ones. Point tables, masks and saved \
      registers reside in `scratch`."])
    code := Impl.Ed25519.X86_64.scalarBase_precomputed Impl.X25519.X86_64.baseline
    contract := Spec.Ed25519.scalarBaseContract X86_64.abi
    verified := Proof.Ed25519.X86_64.scalarBase_precomputed_verified
      (fld := Impl.X25519.X86_64.baseline)
    stack := 0
    spSafe := Code.all_of_allInstrs (by lit_decide) },
  { Spec.Ed25519.scalarBaseApi with
    target := X86_64.target
    name := "vg_ed25519_scalar_base_precomputed_adx"
    doc := Spec.Ed25519.scalarBaseApi.doc (notes := ["The code of \
      `vg_ed25519_scalar_base_precomputed` but for the field multiplications and squarings, \
      which use BMI2's `mulx` and ADX's `adcx` and `adox` (two carry chains at once), as \
      `vg_x25519_adx` does. Its comb selects each of the scalar's 64 signed digits' table entry \
      in constant time; point tables, masks and saved registers reside in `scratch`."])
    code := Impl.Ed25519.X86_64.scalarBase_precomputed Impl.X25519.X86_64.adx
    contract := Spec.Ed25519.scalarBaseContract X86_64.abi
    verified := Proof.Ed25519.X86_64.scalarBase_precomputed_verified (fld := Impl.X25519.X86_64.adx)
    features := ["bmi2", "adx"]
    stack := 0
    spSafe := Code.all_of_allInstrs (by lit_decide) }]

end VG.Artifacts.Ed25519ScalarBase.X86_64
