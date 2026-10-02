import VerifiedGarbage.Proof.MdStream.X86.Finalize
import VerifiedGarbage.Proof.MdStream.X86.Words
import VerifiedGarbage.Proof.Md5.Md
import VerifiedGarbage.Proof.Md5.X86.Contract
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Md5.X86.Compress
import VerifiedGarbage.Impl.Md5.X86.Stream
import VerifiedGarbage.Proof.Md5.X86.Lit

/-!
# Streaming MD5 on x86 (32-bit): `update` and `finalize`

`update` and `finalize` are the generic streaming code
(`Impl/MdStream/X86.lean`), so they are verified by the generic proofs
(`Proof/MdStream/X86/`) for MD5's instance (`Proof/Md5/Md.lean`) with 112
bytes of scratch space, given what MD5's own pieces do: its length field and
digest (`shape`), that its compression function is verified (`callee`), and
that the taint analysis accepts its code (which it checks together with the
compression function's).
-/

namespace VG.Proof.Md5.X86.Stream

open VG VG.X86 VG.Proof.MdStream VG.Proof.MdStream.X86

abbrev params := Impl.Md5.X86.Stream.params

theorem dims : Dims params 112 := ⟨by decide, by decide, by decide⟩

theorem shape : Shape (P := params) md where
  len _ hfit hlo hhi ho₁ ho₂ := len64_ok (so := params.so) (d := params.N + 56) (be := false) (by omega)
    hlo hhi ho₁ ho₂
  out _ hbx hax hin hout hd := by
    refine (out32_ok (n := 4) false (by decide) hbx hax hin hout hd).mono fun s' ⟨g, rd, wr, m⟩ =>
      ⟨g, rd, wr, ?_⟩
    rw [m, digest_eq]

theorem callee : CalleeOk (P := params) md Impl.Md5.X86.compress :=
  ⟨compress_verified.1, NoSp.of_all (by lit_decide), by lit_decide⟩

namespace Update

theorem update_verified : Verified X86.target Impl.Md5.X86.Stream.update Proof.Md5.updateX86 :=
  have h := MdStream.X86.Update.verified (name := "vg_md5_compress") dims callee
    (VG.Taint.constantTime (A := taint) (MdStream.X86.Update.τ₀ params 112)
      (fun _ _ h₁ h₂ hp => MdStream.X86.Update.agree₀ dims h₁ h₂ hp) (by taint_decide))
  Verified.of_implies h ⟨fun _ h => h, fun _ _ _ h m hr hc => h Spec.Md5.H0 m hr hc, fun _ _ _ _ h => h, h.2.2⟩

/-- A state satisfying `update`'s precondition. -/
abbrev sat : State := MdStream.X86.Update.sat params 112

end Update

namespace Finalize

theorem finalize_verified : Verified X86.target Impl.Md5.X86.Stream.finalize Proof.Md5.finalizeX86 :=
  have h := MdStream.X86.Finalize.verified (name := "vg_md5_compress") dims shape callee
    (VG.Taint.constantTime (A := taint) (MdStream.X86.Finalize.τ₀ params 112)
      (fun _ _ h₁ h₂ hp => MdStream.X86.Finalize.agree₀ dims h₁ h₂ hp) (by taint_decide))
  Verified.of_implies h
    ⟨fun _ h => h, fun _ _ _ h m hr hc => h Spec.Md5.H0 m hr trivial hc, fun _ _ _ _ h => h, h.2.2⟩

/-- A state satisfying `finalize`'s precondition. -/
abbrev sat : State := MdStream.X86.Finalize.sat params 112

end Finalize

end VG.Proof.Md5.X86.Stream
