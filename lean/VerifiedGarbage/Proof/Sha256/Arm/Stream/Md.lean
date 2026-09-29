import VerifiedGarbage.Proof.MdStream.Arm.Update
import VerifiedGarbage.Proof.MdStream.Arm.Finalize
import VerifiedGarbage.Proof.MdStream.Arm.Words
import VerifiedGarbage.Proof.Sha256.Md
import VerifiedGarbage.Proof.Sha256.Arm.Contract
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Sha256.Arm.Compress
import VerifiedGarbage.Impl.Sha256.Arm.Stream
import VerifiedGarbage.Proof.Sha256.Arm.Lit

/-!
# Streaming SHA-256 on ARMv7: `update` and `finalize`

Untrusted: everything here is checked by Lean. `update` and `finalize` are
the generic streaming code (`Impl/MdStream/Arm.lean`), so they are verified
by the generic proofs (`Proof/MdStream/Arm/`) for SHA-256's instance
(`Proof/Sha256/Md.lean`), given what SHA-256's own pieces do: its length field and
digest (`shape`), that its compression function is verified (`callee`), and
that the taint analysis accepts its code.
-/

namespace VG.Proof.Sha256.Arm.Stream

open VG VG.Arm VG.Proof.MdStream VG.Proof.MdStream.Arm

abbrev params := Impl.Sha256.Arm.Stream.params

theorem dims : Dims params := ⟨by decide, by decide, by decide⟩

theorem shape : Shape (P := params) md where
  len _ hfit hout := len64_ok (d := params.N + 56) (be := true) (by decide) (by omega) hout
  out _ f₀ f₆ hin hout hd := by
    refine (out32_ok (n := 8) true (by decide) f₀ f₆ hin hout hd).mono fun s' ⟨g, rd, wr, sp, m⟩ =>
      ⟨g, rd, wr, sp, ?_⟩
    rw [m, digest_eq]

theorem callee : CalleeOk (P := params) md Impl.Sha256.Arm.compress :=
  ⟨compress_verified.1, by decide +kernel, by rw [← Code.allInstrs_eq]; decide +kernel⟩

namespace Update

theorem update_verified : Verified Arm.target Impl.Sha256.Arm.Stream.update Proof.Sha256.updateArm :=
  have h := MdStream.Arm.Update.verified (name := "vg_sha256_compress") dims callee
    (VG.Taint.constantTime (A := taint) (MdStream.Arm.Update.τ₀ params)
      (fun _ _ h₁ h₂ hp => MdStream.Arm.Update.agree₀ h₁ h₂ hp) (by taint_decide))
  Verified.of_implies h ⟨fun _ h => h, fun _ _ _ h m hr hc => h Spec.Sha256.H0 m hr hc, fun _ _ _ _ h => h, h.2.2⟩

/-- A state satisfying `update`'s precondition. -/
abbrev sat : State := MdStream.Arm.Update.sat params

end Update

namespace Finalize

theorem finalize_verified : Verified Arm.target Impl.Sha256.Arm.Stream.finalize Proof.Sha256.finalizeArm :=
  have h := MdStream.Arm.Finalize.verified (name := "vg_sha256_compress") dims shape callee
    (VG.Taint.constantTime (A := taint) (MdStream.Arm.Finalize.τ₀ params)
      (fun _ _ h₁ h₂ hp => MdStream.Arm.Finalize.agree₀ h₁ h₂ hp) (by taint_decide))
  Verified.of_implies h
    ⟨fun _ h => h, fun _ _ _ h m hr hc => h Spec.Sha256.H0 m hr trivial hc, fun _ _ _ _ h => h, h.2.2⟩

/-- A state satisfying `finalize`'s precondition. -/
abbrev sat : State := MdStream.Arm.Finalize.sat params

theorem writeW_rev (m : Mem) (a : Addr) (w : BitVec 32) :
    m.writeW a (rev w) = Proof.Sha256.Stream.writeBytes m a (Spec.Sha256.wordBytes w) :=
  writeW_be m a w

theorem flat_length (H : Spec.Sha256.HashValue) (k : Nat) (hk : k ≤ 8) :
    ((H.toList.take k).flatMap Spec.Sha256.wordBytes).length = 4 * k := by
  rw [List.length_flatMap]
  have : ∀ w ∈ H.toList.take k, (Spec.Sha256.wordBytes w).length = 4 := fun w _ => rfl
  rw [List.map_congr_left this, List.map_const', List.sum_replicate_nat, List.length_take]
  simp; omega

end Finalize

end VG.Proof.Sha256.Arm.Stream
