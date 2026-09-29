import VerifiedGarbage.Proof.MdStream.X86_64.UpdateCT
import VerifiedGarbage.Proof.MdStream.X86_64.FinalizeCT
import VerifiedGarbage.Proof.MdStream.X86_64.Words
import VerifiedGarbage.Proof.Md5.Md
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Md5.X86_64.Compress
import VerifiedGarbage.Impl.Md5.X86_64.Stream

/-!
# Streaming MD5 on x86-64: `update` and `finalize`

Untrusted: everything here is checked by Lean. `update` and `finalize` are
the generic streaming code (`Impl/MdStream/X86_64.lean`), so they are
verified by the generic proofs (`Proof/MdStream/X86_64/`) for MD5's
instance (`Proof/Md5/Md.lean`), given what MD5's own pieces do: its length
field and digest (`shape`), that the taint analysis accepts its code between
the calls (`taints`), and that its compression function is verified
(`callee`).
-/

namespace VG.Proof.Md5.X86_64.Stream

open VG VG.X86_64 VG.Proof.MdStream VG.Proof.MdStream.X86_64
open VG.Impl.MdStream.X86_64 (len64 out32)

abbrev params := Impl.Md5.X86_64.Stream.params

theorem dims : Dims params := ⟨.inl rfl, by decide, by decide, by decide⟩

theorem digest_eq (mem : Mem) (p : Addr) :
    md.digest (md.stateAt mem p) = (List.range 4).flatMap fun k =>
      bytes32 false (mem.readW (p + BitVec.ofNat 64 (4 * k)) 32) := by
  simp [md, Spec.Md5.stateAt, Vector.toList_ofFn, List.range_succ, List.ofFn_succ, bytes32, Spec.Md5.wordBytes]

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

theorem callee : CalleeOk (P := params) md Impl.Md5.X86_64.compress :=
  .of_verified compress_verified.1 compress_verified.2.1 (by rw [← Code.allInstrs_eq]; decide +kernel)
    (by decide +kernel)

namespace Update

theorem update_verified : Verified X86_64.target Impl.Md5.X86_64.Stream.update Proof.Md5.updateX86_64 :=
  have h := MdStream.X86_64.Update.verified (name := "vg_md5_compress") dims taints callee (by decide +kernel)
  Verified.of_implies h ⟨fun _ h => h, fun _ _ _ h m hr hc => h Spec.Md5.H0 m hr hc, fun _ _ _ _ h => h, h.2.2⟩

/-- A state satisfying `update`'s precondition. -/
abbrev sat : State := MdStream.X86_64.Update.sat params

end Update

namespace Finalize

theorem finalize_verified : Verified X86_64.target Impl.Md5.X86_64.Stream.finalize Proof.Md5.finalizeX86_64 :=
  have h := MdStream.X86_64.Finalize.verified (name := "vg_md5_compress") dims shape taints callee (by decide +kernel)
  Verified.of_implies h ⟨fun _ h => h, fun _ _ _ h m hr hc => h Spec.Md5.H0 m hr trivial hc, fun _ _ _ _ h => h, h.2.2⟩

/-- A state satisfying `finalize`'s precondition. -/
abbrev sat : State := MdStream.X86_64.Finalize.sat params

end Finalize

end VG.Proof.Md5.X86_64.Stream
