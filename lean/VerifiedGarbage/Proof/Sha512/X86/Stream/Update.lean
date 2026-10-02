import VerifiedGarbage.Proof.Sha512.Md
import VerifiedGarbage.Proof.MdStream.X86.Finalize
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Sha512.X86.Compress
import VerifiedGarbage.Impl.Sha512.X86.Stream
import VerifiedGarbage.Proof.Sha512.X86.Lit

/-!
# Streaming SHA-512 on x86 (32-bit): `update`

`update` and `finalize` are the generic streaming code
(`Impl/MdStream/X86.lean`), so they are verified by the generic proofs
(`Proof/MdStream/X86/`) for the SHA-512 family's instance
(`Proof/Sha512/Md.lean`) with 272 bytes of scratch space, given that its
compression function is verified (`callee`) and that the taint analysis
accepts its code (which it checks together with the compression function's).
`Finalize.lean` adds what the family's length field and digest do.
-/

namespace VG.Proof.Sha512.X86.Stream

open VG VG.X86 VG.Proof.MdStream VG.Proof.MdStream.X86

abbrev params := Impl.Sha512.X86.Stream.params

theorem dims : Dims params 272 := ⟨.inr rfl, by decide, by decide, by decide, by decide⟩

theorem callee : CalleeOk (P := params) md Impl.Sha512.X86.compress :=
  ⟨Compress.compress_verified.1, NoSp.of_all (by lit_decide), by lit_decide⟩

namespace Update

theorem update_verified : Verified X86.target Impl.Sha512.X86.Stream.update Proof.Sha512.updateX86 :=
  MdStream.X86.Update.verified (name := "vg_sha512_compress") dims callee
    (VG.Taint.constantTime (A := taint) (MdStream.X86.Update.τ₀ params 272)
      (fun _ _ h₁ h₂ hp => MdStream.X86.Update.agree₀ dims h₁ h₂ hp) (by taint_decide))

/-- A state satisfying `update`'s precondition. -/
abbrev sat : State := MdStream.X86.Update.sat params 272

end Update

end VG.Proof.Sha512.X86.Stream
