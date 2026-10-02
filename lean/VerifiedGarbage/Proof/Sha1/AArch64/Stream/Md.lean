import VerifiedGarbage.Proof.MdStream.AArch64.Update
import VerifiedGarbage.Proof.MdStream.AArch64.Finalize
import VerifiedGarbage.Proof.MdStream.AArch64.Words
import VerifiedGarbage.Proof.Sha1.Md
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Sha1.AArch64.Compress
import VerifiedGarbage.Impl.Sha1.AArch64.Stream

/-!
# Streaming SHA-1 on AArch64: `update` and `finalize`

`update` and `finalize` are the generic streaming code
(`Impl/MdStream/AArch64.lean`), so they are verified by the generic proofs
(`Proof/MdStream/AArch64/`) for SHA-1's instance (`Proof/Sha1/Md.lean`), given
what SHA-1's own pieces do: its length field and digest (`shape`), that its
compression function is verified (`callee`), and that the taint analysis
accepts its code.
-/

namespace VG.Proof.Sha1.AArch64.Stream

open VG VG.AArch64 VG.Proof.MdStream VG.Proof.MdStream.AArch64

abbrev params := Impl.Sha1.AArch64.Stream.params

theorem dims : Dims params := ⟨by decide, by decide, by decide, by decide⟩

theorem shape : Shape (P := params) md where
  lenKeepsV := by decide +kernel
  outKeepsV := by decide +kernel
  len _ hout := len64_ok (d := params.N + params.B - params.L) (be := true) (by decide) hout
  out _ hin hout hd := by
    refine (out32_ok (n := 5) true (by decide) hin hout hd).mono fun s' ⟨g, rd, wr, sp, m⟩ =>
      ⟨g, rd, wr, sp, ?_⟩
    rw [m, digest_eq]

theorem callee : CalleeOk (P := params) md Impl.Sha1.AArch64.compress :=
  ⟨compress_verified.1, by lit_decide, by lit_decide⟩

namespace Update

theorem update_verified : Verified AArch64.target Impl.Sha1.AArch64.Stream.update Proof.Sha1.updateAArch64 :=
  have h := MdStream.AArch64.Update.verified (name := "vg_sha1_compress") dims callee
    (VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0, .x1, .x2, .x3, .x4])
      (fun _ _ _ _ hp => MdStream.AArch64.Update.agree₀ hp) (by taint_decide))
    (instrs_keeps (by lit_decide)) (by lit_decide)
  Verified.of_implies h ⟨fun _ h => h, fun _ _ _ h m hr hc => h Spec.Sha1.H0 m hr hc, fun _ _ _ _ h => h, h.2.2⟩

/-- A state satisfying `update`'s precondition. -/
abbrev sat : State := MdStream.AArch64.Update.sat params

end Update

namespace Finalize

theorem finalize_verified : Verified AArch64.target Impl.Sha1.AArch64.Stream.finalize Proof.Sha1.finalizeAArch64 :=
  have h := MdStream.AArch64.Finalize.verified (name := "vg_sha1_compress") dims shape callee
    (VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0, .x1, .x2, .x3])
      (fun _ _ _ _ hp => MdStream.AArch64.Finalize.agree₀ hp) (by taint_decide))
    (instrs_keeps (by lit_decide)) (by lit_decide)
  Verified.of_implies h
    ⟨fun _ h => h, fun _ _ _ h m hr hc => h Spec.Sha1.H0 m hr trivial hc, fun _ _ _ _ h => h, h.2.2⟩

/-- A state satisfying `finalize`'s precondition. -/
abbrev sat : State := MdStream.AArch64.Finalize.sat params

end Finalize

end VG.Proof.Sha1.AArch64.Stream
