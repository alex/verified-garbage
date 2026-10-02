import VerifiedGarbage.Proof.MdStream.Arm.Update
import VerifiedGarbage.Proof.Sha512.Md
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Sha512.Arm.Compress
import VerifiedGarbage.Impl.Sha512.Arm.Stream
import VerifiedGarbage.Proof.Sha512.Arm.Lit

/-!
# Streaming SHA-512 on ARMv7: `update`

`update` is the generic streaming code (`Impl/MdStream/Arm.lean`), so it is
verified by the generic proof (`Proof/MdStream/Arm/Update.lean`) for the
SHA-512 family's instance (`Proof/Sha512/Md.lean`), given that its compression
function is verified (`callee`) and that the taint analysis accepts its code.
-/

namespace VG.Proof.Sha512.Arm.Stream

open VG VG.Arm VG.Proof.MdStream VG.Proof.MdStream.Arm

abbrev params := Impl.Sha512.Arm.Stream.params

theorem dims : Dims params := ⟨.inr rfl, by decide, by decide, by decide, by decide, by decide⟩

theorem callee : CalleeOk (P := params) Proof.Sha512.md Impl.Sha512.Arm.compress :=
  ⟨Compress.compress_verified.1, by lit_decide, by rw [← Code.allInstrs_eq]; lit_decide⟩

namespace Update

theorem update_verified : Verified Arm.target Impl.Sha512.Arm.Stream.update Proof.Sha512.updateArm :=
  have h := MdStream.Arm.Update.verified (name := "vg_sha512_compress") dims callee
    (VG.Taint.constantTime (A := taint) (MdStream.Arm.Update.τ₀ params)
      (fun _ _ h₁ h₂ hp => MdStream.Arm.Update.agree₀ h₁ h₂ hp) (by taint_decide))
  Verified.of_implies h ⟨fun _ h => h, fun _ _ _ h iv m hr hc => h iv m hr hc, fun _ _ _ _ h => h, h.2.2⟩

/-- A state satisfying `update`'s precondition. -/
abbrev sat : State := MdStream.Arm.Update.sat params

end Update

end VG.Proof.Sha512.Arm.Stream
