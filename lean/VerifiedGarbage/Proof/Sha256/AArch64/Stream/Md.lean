import VerifiedGarbage.Proof.MdStream.AArch64.Update
import VerifiedGarbage.Proof.MdStream.AArch64.Finalize
import VerifiedGarbage.Proof.MdStream.AArch64.Words
import VerifiedGarbage.Proof.Sha256.Md
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Sha256.AArch64.Compress
import VerifiedGarbage.Proof.Sha256.Stream
import VerifiedGarbage.Impl.Sha256.AArch64.Stream
import VerifiedGarbage.Proof.Sha256.AArch64.Lit

/-!
# Streaming SHA-256 on AArch64: `update` and `finalize`

Untrusted: everything here is checked by Lean. `update` and `finalize` are
the generic streaming code (`Impl/MdStream/AArch64.lean`), so they are
verified by the generic proofs (`Proof/MdStream/AArch64/`) for SHA-256's
instance (`Proof/Sha256/Md.lean`), given what SHA-256's own pieces do: its length
field and digest (`shape`), that its compression function is verified
(`callee`), and that the taint analysis accepts its code.
-/

namespace VG.Proof.Sha256.AArch64.Stream

open VG VG.AArch64 VG.Proof.MdStream VG.Proof.MdStream.AArch64

abbrev params := Impl.Sha256.AArch64.Stream.params

theorem dims : Dims params := ⟨by decide, by decide⟩

theorem shape : Shape (P := params) md where
  lenKeepsV := by decide +kernel
  outKeepsV := by decide +kernel
  len _ hout := len64_ok (d := params.N + 56) (be := true) (by decide) hout
  out _ hin hout hd := by
    refine (out32_ok (n := 8) true (by decide) hin hout hd).mono fun s' ⟨g, rd, wr, sp, m⟩ =>
      ⟨g, rd, wr, sp, ?_⟩
    rw [m, digest_eq]

theorem callee : CalleeOk (P := params) md Impl.Sha256.AArch64.compress :=
  ⟨compress_verified.1, by lit_decide, by lit_decide⟩

namespace Update

theorem update_verified : Verified AArch64.target Impl.Sha256.AArch64.Stream.update Proof.Sha256.updateAArch64 :=
  have h := MdStream.AArch64.Update.verified (name := "vg_sha256_compress") dims callee
    (VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0, .x1, .x2, .x3, .x4])
      (fun _ _ _ _ hp => MdStream.AArch64.Update.agree₀ hp) (by taint_decide))
    (instrs_keeps (by lit_decide)) (by lit_decide)
  Verified.of_implies h ⟨fun _ h => h, fun _ _ _ h iv m hr hc => h iv m hr hc, fun _ _ _ _ h => h, h.2.2⟩

/-- A state satisfying `update`'s precondition. -/
abbrev sat : State := MdStream.AArch64.Update.sat params

end Update

namespace Finalize

theorem finalize_verified : Verified AArch64.target Impl.Sha256.AArch64.Stream.finalize Proof.Sha256.finalizeAArch64 :=
  have h := MdStream.AArch64.Finalize.verified (name := "vg_sha256_compress") dims shape callee
    (VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0, .x1, .x2, .x3])
      (fun _ _ _ _ hp => MdStream.AArch64.Finalize.agree₀ hp) (by taint_decide))
    (instrs_keeps (by lit_decide)) (by lit_decide)
  Verified.of_implies h
    ⟨fun _ h => h, fun _ _ _ h iv m hr hc => h iv m hr trivial hc, fun _ _ _ _ h => h, h.2.2⟩

/-- A state satisfying `finalize`'s precondition. -/
abbrev sat : State := MdStream.AArch64.Finalize.sat params

theorem writeW_rev32 (m : Mem) (a : Addr) (w : BitVec 32) :
    m.writeW a (rev32 w) = Proof.Sha256.Stream.writeBytes m a (Spec.Sha256.wordBytes w) :=
  writeW32 m a true w

theorem sw32 (v : BitVec 32) : (v.setWidth 64).setWidth 32 = v := setWidth32 v

theorem flat_length (H : Spec.Sha256.HashValue) (k : Nat) (hk : k ≤ 8) :
    ((H.toList.take k).flatMap Spec.Sha256.wordBytes).length = 4 * k := by
  rw [List.length_flatMap]
  have : ∀ w ∈ H.toList.take k, (Spec.Sha256.wordBytes w).length = 4 := fun w _ => rfl
  rw [List.map_congr_left this, List.map_const', List.sum_replicate_nat, List.length_take]
  simp; omega

end Finalize

end VG.Proof.Sha256.AArch64.Stream
