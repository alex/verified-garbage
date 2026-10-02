import VerifiedGarbage.Proof.MdStream.AArch64.Update
import VerifiedGarbage.Proof.MdStream.AArch64.Finalize
import VerifiedGarbage.Proof.MdStream.AArch64.Words
import VerifiedGarbage.Proof.Sha512.Md
import VerifiedGarbage.Proof.Sha512.AArch64.Compress
import VerifiedGarbage.Impl.Sha512.AArch64.Stream

/-!
# Streaming SHA-512 on AArch64: `update` and `finalize`

`update` and `finalize` are the generic streaming code
(`Impl/MdStream/AArch64.lean`), so they are verified by the generic proofs
(`Proof/MdStream/AArch64/`) for the SHA-512 family's instance
(`Proof/Sha512/Md.lean`), for any implementation of the compression function
(`Proof/Sha512/AArch64/Variant.lean`), given what the family's own pieces do:
its length field and digest (`shape`).
-/

namespace VG.Proof.Sha512.AArch64.Stream

open VG VG.AArch64 VG.Proof.MdStream VG.Proof.MdStream.AArch64
open VG.Proof.Sha256.Stream (writeBytes)

abbrev params := Impl.Sha512.AArch64.Stream.params

theorem dims : Dims params := ⟨by decide, by decide, by decide, by decide⟩

theorem digest_eq (mem : Mem) (p : Addr) :
    md.digest (md.stateAt mem p) = (List.range 8).flatMap fun k =>
      bytes64 true (mem.readW (p + BitVec.ofNat 64 (8 * k)) 64) := by
  simp [md, Spec.Sha512.stateAt, Vector.toList_ofFn, List.range_succ, List.ofFn_succ, bytes64,
    Spec.Sha512.wordBytes]

theorem shape : Shape (P := params) md where
  lenKeepsV := by decide +kernel
  outKeepsV := by decide +kernel
  len _ hout := (len128_ok (d := 176) (by decide) hout).mono fun s' ⟨g, rd, wr, sp, m⟩ =>
    ⟨g, rd, wr, sp, by rw [m, lenOf_split]; rfl⟩
  out _ hin hout hd := by
    refine (out64_ok (n := 8) (by decide) hin hout hd).mono fun s' ⟨g, rd, wr, sp, m⟩ =>
      ⟨g, rd, wr, sp, ?_⟩
    rw [m, digest_eq]

/-- A state satisfying `update`'s precondition. -/
abbrev Update.sat : State := MdStream.AArch64.Update.sat params

/-- A state satisfying `finalize`'s precondition. -/
abbrev Finalize.sat : State := MdStream.AArch64.Finalize.sat params

end VG.Proof.Sha512.AArch64.Stream
