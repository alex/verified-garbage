import VerifiedGarbage.Proof.MdStream.AArch64.Update
import VerifiedGarbage.Proof.MdStream.AArch64.Finalize
import VerifiedGarbage.Proof.MdStream.AArch64.Words
import VerifiedGarbage.Proof.Md5.Md
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Md5.AArch64.Compress
import VerifiedGarbage.Impl.Md5.AArch64.Stream

/-!
# Streaming MD5 on AArch64: `update` and `finalize`

Untrusted: everything here is checked by Lean. `update` and `finalize` are
the generic streaming code (`Impl/MdStream/AArch64.lean`), so they are
verified by the generic proofs (`Proof/MdStream/AArch64/`) for MD5's
instance (`Proof/Md5/Md.lean`), given what MD5's own pieces do: its length
field and digest (`shape`), that its compression function is verified
(`callee`), and that the taint analysis accepts its code.
-/

namespace VG.Proof.Md5.AArch64.Stream

open VG VG.AArch64 VG.Proof.MdStream VG.Proof.MdStream.AArch64

abbrev params := Impl.Md5.AArch64.Stream.params

theorem dims : Dims params := ⟨by decide, by decide⟩

theorem shape : Shape (P := params) md where
  len _ hout := len64_ok (d := params.N + 56) (be := false) (by decide) hout
  out _ hin hout hd := by
    refine (out32_ok (n := 4) false (by decide) hin hout hd).mono fun s' ⟨g, rd, wr, sp, m⟩ =>
      ⟨g, rd, wr, sp, ?_⟩
    rw [m, digest_eq]

theorem callee : CalleeOk (P := params) md Impl.Md5.AArch64.compress :=
  ⟨compress_verified.1, by decide +kernel⟩

namespace Update

theorem update_verified : Verified AArch64.target Impl.Md5.AArch64.Stream.update Proof.Md5.updateAArch64 :=
  have h := MdStream.AArch64.Update.verified (name := "vg_md5_compress") dims callee
    (VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0, .x1, .x2, .x3, .x4])
      (fun _ _ _ _ hp => MdStream.AArch64.Update.agree₀ hp) (by taint_decide))
    (instrs_keeps (by decide +kernel)) (by decide +kernel)
  Verified.of_implies h ⟨fun _ h => h, fun _ _ _ h m hr hc => h Spec.Md5.H0 m hr hc, fun _ _ _ _ h => h, h.2.2⟩

/-- A state satisfying `update`'s precondition. -/
abbrev sat : State := MdStream.AArch64.Update.sat params

end Update

namespace Finalize

theorem finalize_verified : Verified AArch64.target Impl.Md5.AArch64.Stream.finalize Proof.Md5.finalizeAArch64 :=
  have h := MdStream.AArch64.Finalize.verified (name := "vg_md5_compress") dims shape callee
    (VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0, .x1, .x2, .x3])
      (fun _ _ _ _ hp => MdStream.AArch64.Finalize.agree₀ hp) (by taint_decide))
    (instrs_keeps (by decide +kernel)) (by decide +kernel)
  Verified.of_implies h
    ⟨fun _ h => h, fun _ _ _ h m hr hc => h Spec.Md5.H0 m hr trivial hc, fun _ _ _ _ h => h, h.2.2⟩

/-- A state satisfying `finalize`'s precondition. -/
abbrev sat : State := MdStream.AArch64.Finalize.sat params

end Finalize

end VG.Proof.Md5.AArch64.Stream
