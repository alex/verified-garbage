import VerifiedGarbage.Proof.Sha256.X86.Shared

/-!
# Streaming SHA-256 parameterized by compression on x86

The functional and ABI proofs hold once for every verified compression
function. Each backend supplies constant-time certificates for its emitted
streaming code, checked against the same streaming contracts.
-/
namespace VG.Proof.Sha256.X86.Stream

open VG.X86
open VG.Proof.MdStream VG.Proof.MdStream.X86

variable {name : String} {code : Prog isa}
  (hcomp : CalleeOk (P := params) md code)
include hcomp

/-- Any verified compressor gives the same SHA-256 update contract. -/
theorem update_of (ct : ConstantTime isa (updK (P := params) md 160).pre
    (updK (P := params) md 160).pub (Impl.MdStream.X86.update params name code)) :
    Verified X86.target (Impl.MdStream.X86.update params name code) Proof.Sha256.updateX86 := by
  have h := MdStream.X86.Update.verified (name := name) dims hcomp ct
  exact Verified.of_implies h
    ⟨fun _ h => h, fun _ _ _ h m hr hc => h Spec.Sha256.H0 m hr hc,
      fun _ _ _ _ h => h, h.2.2⟩

/-- Any verified compressor gives the same SHA-256 finalization contract. -/
theorem finalize_of (ct : ConstantTime isa (finK (P := params) md 160).pre
    (finK (P := params) md 160).pub (Impl.MdStream.X86.finalize params name code)) :
    Verified X86.target (Impl.MdStream.X86.finalize params name code) Proof.Sha256.finalizeX86 := by
  have h := MdStream.X86.Finalize.verified (name := name) dims shape hcomp ct
  exact Verified.of_implies h
    ⟨fun _ h => h, fun _ _ _ h m hr hc => h Spec.Sha256.H0 m hr trivial hc,
      fun _ _ _ _ h => h, h.2.2⟩

end VG.Proof.Sha256.X86.Stream
