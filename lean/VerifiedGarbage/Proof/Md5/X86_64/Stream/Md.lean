import VerifiedGarbage.Proof.MdStream.X86_64.UpdateCT
import VerifiedGarbage.Proof.MdStream.X86_64.FinalizeCT
import VerifiedGarbage.Proof.MdStream.X86_64.Words
import VerifiedGarbage.Proof.Md5.Md
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Md5.X86_64.Compress
import VerifiedGarbage.Proof.Md5.X86_64.Avx512.Compress
import VerifiedGarbage.Impl.Md5.X86_64.Stream

/-!
# Streaming MD5 on x86-64: `update` and `finalize`

`update` and `finalize` are the generic streaming code
(`Impl/MdStream/X86_64.lean`), so they are verified by the generic proofs
(`Proof/MdStream/X86_64/`) for MD5's instance (`Proof/Md5/Md.lean`), for
any implementation `f` of the compression function (`CalleeOk`: `scalar_ok`,
`avx512_ok`), given what MD5's own pieces do: its length field and digest
(`shape`) and that the taint analysis accepts its code between the calls
(`taints`).
-/

namespace VG.Proof.Md5.X86_64.Stream

open VG VG.X86_64 VG.Proof.MdStream VG.Proof.MdStream.X86_64
open VG.Impl.MdStream.X86_64 (len64 out32)
open VG.Impl.Md5.X86_64.Stream (Callee update finalize)

abbrev params := Impl.Md5.X86_64.Stream.params

theorem dims : Dims params := ⟨.inl rfl, by decide, by decide, by decide⟩

theorem shape : Shape (P := params) md where
  len s hout := by
    rw [show params.len = len64 72 false ++ [] from rfl]
    exact len64_ok hout fun s' g rd wr m => WP.block_nil ⟨g, rd, wr, m⟩
  out s hin hout hd := by
    refine (out32_ok (n := 4) false (by decide) hin hout hd).mono fun s' ⟨g, rd, wr, m⟩ => ⟨g, rd, wr, ?_⟩
    rw [m, digest_eq]

theorem taints : Taints params :=
  ⟨⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩,
    ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩⟩

theorem scalar_ok : CalleeOk (P := params) md Callee.scalar.code :=
  .of_verified compress_verified.1 compress_verified.2.1 (by rw [← Code.allInstrs_eq]; lit_decide)
    (by lit_decide)

theorem avx512_ok : CalleeOk (P := params) md Callee.avx512.code :=
  .of_verified Avx512.compress_verified.1 Avx512.compress_verified.2.1
    (by rw [← Code.allInstrs_eq]; lit_decide) (by lit_decide)

namespace Update

/-- `update` is verified if it never loads MXCSR. -/
theorem verified_of {f : Callee} (hf : CalleeOk (P := params) md f.code)
    (hm : (update f).allInstrs (fun i => !loadsMxcsr i) = true) :
    Verified X86_64.target (update f) Proof.Md5.updateX86_64 :=
  have h := MdStream.X86_64.Update.verified dims taints hf hm
  Verified.of_implies h ⟨fun _ h => h, fun _ _ _ h m hr hc => h Spec.Md5.H0 m hr hc, fun _ _ _ _ h => h, h.2.2⟩

/-- A state satisfying `update`'s precondition. -/
abbrev sat : State := MdStream.X86_64.Update.sat params

end Update

namespace Finalize

/-- `finalize` is verified if it never loads MXCSR. -/
theorem verified_of {f : Callee} (hf : CalleeOk (P := params) md f.code)
    (hm : (finalize f).allInstrs (fun i => !loadsMxcsr i) = true) :
    Verified X86_64.target (finalize f) Proof.Md5.finalizeX86_64 :=
  have h := MdStream.X86_64.Finalize.verified dims shape taints hf hm
  Verified.of_implies h ⟨fun _ h => h, fun _ _ _ h m hr hc => h Spec.Md5.H0 m hr trivial hc, fun _ _ _ _ h => h, h.2.2⟩

/-- A state satisfying `finalize`'s precondition. -/
abbrev sat : State := MdStream.X86_64.Finalize.sat params

end Finalize

end VG.Proof.Md5.X86_64.Stream
