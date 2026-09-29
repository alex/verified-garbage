import VerifiedGarbage.Proof.MdStream.X86_64.UpdateCT
import VerifiedGarbage.Proof.MdStream.X86_64.FinalizeCT
import VerifiedGarbage.Proof.MdStream.X86_64.Words
import VerifiedGarbage.Proof.Sha1.Md
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Sha1.X86_64.Compress
import VerifiedGarbage.Impl.Sha1.X86_64.Stream

/-!
# Streaming SHA-1 on x86-64: `update` and `finalize`

Untrusted: everything here is checked by Lean. `update` and `finalize` are
the generic streaming code (`Impl/MdStream/X86_64.lean`), so they are
verified by the generic proofs (`Proof/MdStream/X86_64/`) for SHA-1's
instance (`Proof/Sha1/Md.lean`), given what SHA-1's own pieces do: its length
field and digest (`shape`), that the taint analysis accepts its code between
the calls (`taints`), and that its compression function is verified
(`callee`).
-/

namespace VG.Proof.Sha1.X86_64.Stream

open VG VG.X86_64 VG.Proof.MdStream VG.Proof.MdStream.X86_64
open VG.Impl.MdStream.X86_64 (len64 out32)

abbrev params := Impl.Sha1.X86_64.Stream.params

theorem dims : Dims params := ⟨.inl rfl, by decide, by decide, by decide⟩

theorem shape : Shape (P := params) md where
  len s hout := by
    rw [show params.len = len64 76 true ++ [] from rfl]
    exact len64_ok hout fun s' g rd wr m => WP.block_nil ⟨g, rd, wr, m⟩
  out s hin hout hd := by
    refine (out32_ok (n := 5) true (by decide) hin hout hd).mono fun s' ⟨g, rd, wr, m⟩ => ⟨g, rd, wr, ?_⟩
    rw [m, digest_eq]

theorem taints : Taints params :=
  ⟨⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩,
    ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩⟩

theorem callee : CalleeOk (P := params) md Impl.Sha1.X86_64.compress :=
  .of_verified compress_verified.1 compress_verified.2.1 (by rw [← Code.allInstrs_eq]; decide +kernel)
    (by decide +kernel)

namespace Update

theorem update_verified : Verified X86_64.target Impl.Sha1.X86_64.Stream.update Proof.Sha1.updateX86_64 :=
  have h := MdStream.X86_64.Update.verified (name := "vg_sha1_compress") dims taints callee (by decide +kernel)
  Verified.of_implies h ⟨fun _ h => h, fun _ _ _ h m hr hc => h Spec.Sha1.H0 m hr hc, fun _ _ _ _ h => h, h.2.2⟩

/-- A state satisfying `update`'s precondition. -/
abbrev sat : State := MdStream.X86_64.Update.sat params

end Update

namespace Finalize

theorem finalize_verified : Verified X86_64.target Impl.Sha1.X86_64.Stream.finalize Proof.Sha1.finalizeX86_64 :=
  have h := MdStream.X86_64.Finalize.verified (name := "vg_sha1_compress") dims shape taints callee (by decide +kernel)
  Verified.of_implies h ⟨fun _ h => h, fun _ _ _ h m hr hc => h Spec.Sha1.H0 m hr trivial hc, fun _ _ _ _ h => h, h.2.2⟩

/-- A state satisfying `finalize`'s precondition. -/
abbrev sat : State := MdStream.X86_64.Finalize.sat params

end Finalize

end VG.Proof.Sha1.X86_64.Stream
