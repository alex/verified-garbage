import VerifiedGarbage.Proof.MdStream.X86_64.UpdateCT
import VerifiedGarbage.Proof.MdStream.X86_64.FinalizeCT
import VerifiedGarbage.Proof.MdStream.X86_64.Words
import VerifiedGarbage.Proof.Sha1.Md
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Sha1.X86_64.Compress
import VerifiedGarbage.Proof.Sha1.X86_64.ShaNi.Compress
import VerifiedGarbage.Impl.Sha1.X86_64.Stream

/-!
# Streaming SHA-1 on x86-64: `update` and `finalize`

Untrusted: everything here is checked by Lean. `update` and `finalize` are
the generic streaming code (`Impl/MdStream/X86_64.lean`), so they are
verified by the generic proofs (`Proof/MdStream/X86_64/`) for SHA-1's
instance (`Proof/Sha1/Md.lean`), for any implementation `f` of the
compression function (`CalleeOk`: `scalar_ok`, `shani_ok`), given what
SHA-1's own pieces do: its length field and digest (`shape`) and that the
taint analysis accepts its code between the calls (`taints`).
-/

namespace VG.Proof.Sha1.X86_64.Stream

open VG VG.X86_64 VG.Proof.MdStream VG.Proof.MdStream.X86_64
open VG.Impl.MdStream.X86_64 (len64 out32)
open VG.Impl.Sha1.X86_64.Stream (Callee update finalize)

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

theorem scalar_ok : CalleeOk (P := params) md Callee.scalar.code :=
  .of_verified compress_verified.1 compress_verified.2.1 (by rw [← Code.allInstrs_eq]; decide +kernel)
    (by decide +kernel)

theorem shani_ok : CalleeOk (P := params) md Callee.shani.code :=
  .of_verified ShaNi.compress_verified.1 ShaNi.compress_verified.2.1
    (by rw [← Code.allInstrs_eq]; decide +kernel) (by decide +kernel)

namespace Update

/-- `update` is verified if it never loads MXCSR. -/
theorem verified_of {f : Callee} (hf : CalleeOk (P := params) md f.code)
    (hm : (update f).allInstrs (fun i => !loadsMxcsr i) = true) :
    Verified X86_64.target (update f) Proof.Sha1.updateX86_64 :=
  have h := MdStream.X86_64.Update.verified dims taints hf hm
  Verified.of_implies h ⟨fun _ h => h, fun _ _ _ h m hr hc => h Spec.Sha1.H0 m hr hc, fun _ _ _ _ h => h, h.2.2⟩

theorem update_verified : Verified X86_64.target (update .scalar) Proof.Sha1.updateX86_64 :=
  verified_of scalar_ok (by decide +kernel)

/-- A state satisfying `update`'s precondition. -/
abbrev sat : State := MdStream.X86_64.Update.sat params

end Update

namespace Finalize

/-- `finalize` is verified if it never loads MXCSR. -/
theorem verified_of {f : Callee} (hf : CalleeOk (P := params) md f.code)
    (hm : (finalize f).allInstrs (fun i => !loadsMxcsr i) = true) :
    Verified X86_64.target (finalize f) Proof.Sha1.finalizeX86_64 :=
  have h := MdStream.X86_64.Finalize.verified dims shape taints hf hm
  Verified.of_implies h ⟨fun _ h => h, fun _ _ _ h m hr hc => h Spec.Sha1.H0 m hr trivial hc, fun _ _ _ _ h => h, h.2.2⟩

theorem finalize_verified : Verified X86_64.target (finalize .scalar) Proof.Sha1.finalizeX86_64 :=
  verified_of scalar_ok (by decide +kernel)

/-- A state satisfying `finalize`'s precondition. -/
abbrev sat : State := MdStream.X86_64.Finalize.sat params

end Finalize

end VG.Proof.Sha1.X86_64.Stream
