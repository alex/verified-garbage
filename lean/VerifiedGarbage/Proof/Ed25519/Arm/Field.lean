import VerifiedGarbage.Impl.Ed25519.Arm.Word
import VerifiedGarbage.Proof.X25519.Arm.Field

/-!
# Ed25519 on ARMv7: field elements in the working space

The field arithmetic is X25519's (`Proof/X25519/Arm/Field`, `AddSub`, `Mul`,
`Cswap`, `Slots`), in a working space of 8192 bytes (`Ctx`) with the product
at `ACC`.
-/

namespace VG.Proof.Ed25519.Arm

open VG.Impl.Ed25519.Arm

/-- `r0` holds the working space `b`, 8192 writable bytes. -/
abbrev Ctx := Proof.X25519.Arm.CtxN 4096

theorem ACC_eq : ACC = 1472 := rfl

end VG.Proof.Ed25519.Arm
