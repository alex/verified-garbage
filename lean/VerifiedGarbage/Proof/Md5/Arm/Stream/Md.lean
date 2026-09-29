import VerifiedGarbage.Proof.MdStream.Arm.Update
import VerifiedGarbage.Proof.MdStream.Arm.Finalize
import VerifiedGarbage.Proof.MdStream.Arm.Words
import VerifiedGarbage.Proof.Md5.Md
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Md5.Arm.Compress
import VerifiedGarbage.Impl.Md5.Arm.Stream

/-!
# Streaming MD5 on ARMv7: `update` and `finalize`

Untrusted: everything here is checked by Lean. `update` and `finalize` are
the generic streaming code (`Impl/MdStream/Arm.lean`), so they are verified
by the generic proofs (`Proof/MdStream/Arm/`) for MD5's instance
(`Proof/Md5/Md.lean`), given what MD5's own pieces do: its length field and
digest (`shape`), that its compression function is verified (`callee`), and
that the taint analysis accepts its code.
-/

namespace VG.Proof.Md5.Arm.Stream

open VG VG.Arm VG.Proof.MdStream VG.Proof.MdStream.Arm

abbrev params := Impl.Md5.Arm.Stream.params

theorem dims : Dims params := ⟨by decide, by decide, by decide⟩

theorem shape : Shape (P := params) md where
  len _ hfit hout := len64_ok (d := params.N + 56) (be := false) (by decide) (by omega) hout
  out _ f₀ f₆ hin hout hd := by
    refine (out32_ok (n := 4) false (by decide) f₀ f₆ hin hout hd).mono fun s' ⟨g, rd, wr, sp, m⟩ =>
      ⟨g, rd, wr, sp, ?_⟩
    rw [m, digest_eq]

theorem callee : CalleeOk (P := params) md Impl.Md5.Arm.compress :=
  ⟨compress_verified.1, by decide +kernel, by rw [← Code.allInstrs_eq]; decide +kernel⟩

namespace Update

theorem update_verified : Verified Arm.target Impl.Md5.Arm.Stream.update Proof.Md5.updateArm :=
  have h := MdStream.Arm.Update.verified (name := "vg_md5_compress") dims callee
    (VG.Taint.constantTime (A := taint) (MdStream.Arm.Update.τ₀ params)
      (fun _ _ h₁ h₂ hp => MdStream.Arm.Update.agree₀ h₁ h₂ hp) (by taint_decide))
  Verified.of_implies h ⟨fun _ h => h, fun _ _ _ h m hr hc => h Spec.Md5.H0 m hr hc, fun _ _ _ _ h => h, h.2.2⟩

/-- A state satisfying `update`'s precondition. -/
abbrev sat : State := MdStream.Arm.Update.sat params

end Update

namespace Finalize

theorem finalize_verified : Verified Arm.target Impl.Md5.Arm.Stream.finalize Proof.Md5.finalizeArm :=
  have h := MdStream.Arm.Finalize.verified (name := "vg_md5_compress") dims shape callee
    (VG.Taint.constantTime (A := taint) (MdStream.Arm.Finalize.τ₀ params)
      (fun _ _ h₁ h₂ hp => MdStream.Arm.Finalize.agree₀ h₁ h₂ hp) (by taint_decide))
  Verified.of_implies h
    ⟨fun _ h => h, fun _ _ _ h m hr hc => h Spec.Md5.H0 m hr trivial hc, fun _ _ _ _ h => h, h.2.2⟩

/-- A state satisfying `finalize`'s precondition. -/
abbrev sat : State := MdStream.Arm.Finalize.sat params

end Finalize

end VG.Proof.Md5.Arm.Stream
