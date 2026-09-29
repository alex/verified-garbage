import VerifiedGarbage.Proof.Sha1.X86_64.Stream.Md

/-!
# Implementations of the SHA-1 compression function on x86-64

Untrusted: everything here is checked by Lean.

A `Compress` is what a function that calls the compression function needs
of it, so that its proof holds for every implementation: each is a variant
of the interface `Sha1Compress` on x86-64
(`Variants/Sha1Compress/X86_64/`), and each caller (in
`Generic/Sha1Compress/X86_64/`) is emitted once for each of them (see
`TCB/Emit.lean`). The streaming functions made with any of them are
verified (`Compress.update_verified`, `Compress.finalize_verified`), and have
what callers of those need (their call depth, that they keep `rsp` and never
load MXCSR), so that a caller of them is proven once for every
implementation.
-/

namespace VG.Proof.Sha1.X86_64

open VG.X86_64

/-- An implementation of the SHA-1 compression function on x86-64. -/
structure Compress where
  /-- Its symbol and code. -/
  callee : Impl.Sha1.X86_64.Stream.Callee
  /-- It is correct and constant time, and keeps what callers need. -/
  ok : MdStream.X86_64.CalleeOk (P := Stream.params) md callee.code
  /-- It never loads MXCSR. -/
  mxcsr : callee.code.allInstrs (fun i => !loadsMxcsr i) = true
  /-- It never writes the stack pointer. -/
  spSafe : callee.code.all (fun i => !isa.writesSp i) = true
  /-- What the names of its callers' instances end with (e.g. `_shani`;
  nothing for the baseline implementation). -/
  suffix : String
  /-- The CPU features its code requires, which its callers require too. -/
  features : List String

namespace Compress

/-- The scalar implementation, `vg_sha1_compress`, in the baseline ISA
(`Variants/Sha1Compress/X86_64/Scalar.lean`). -/
def scalar : Compress where
  callee := .scalar
  ok := Stream.scalar_ok
  mxcsr := by decide +kernel
  spSafe := Code.all_of_allInstrs (by lit_decide)
  suffix := ""
  features := []

open VG.Impl.Sha1.X86_64.Stream (update finalize)

variable (v : Compress)

theorem update_mxcsr : (update v.callee).allInstrs (fun i => !loadsMxcsr i) = true := by
  simp only [update, Impl.MdStream.X86_64.update, Impl.MdStream.X86_64.updateBody,
    Impl.MdStream.X86_64.updateTail, Impl.MdStream.X86_64.compressAt, Code.allInstrs, v.mxcsr,
    Bool.true_and]
  decide +kernel

theorem finalize_mxcsr : (finalize v.callee).allInstrs (fun i => !loadsMxcsr i) = true := by
  simp only [finalize, Impl.MdStream.X86_64.finalize, Impl.MdStream.X86_64.finalizeBody,
    Impl.MdStream.X86_64.compressAt, Code.allInstrs, v.mxcsr, Bool.true_and]
  decide +kernel

theorem update_verified : Verified X86_64.target (update v.callee) Proof.Sha1.updateX86_64 :=
  Stream.Update.verified_of v.ok v.update_mxcsr

theorem finalize_verified : Verified X86_64.target (finalize v.callee) Proof.Sha1.finalizeX86_64 :=
  Stream.Finalize.verified_of v.ok v.finalize_mxcsr

theorem update_depth : (update v.callee).depth = 1 := by
  simp only [update, Impl.MdStream.X86_64.update, Impl.MdStream.X86_64.updateBody,
    Impl.MdStream.X86_64.updateTail, Impl.MdStream.X86_64.compressAt, Code.depth, v.ok.depth]
  decide +kernel

theorem finalize_depth : (finalize v.callee).depth = 1 := by
  simp only [finalize, Impl.MdStream.X86_64.finalize, Impl.MdStream.X86_64.finalizeBody,
    Impl.MdStream.X86_64.compressAt, Code.depth, v.ok.depth]
  decide +kernel

theorem callee_nosp : (v.callee.code.allInstrs fun i => !Taint.clobbers i .rsp) = true := by
  rw [Code.allInstrs_eq]; exact List.all_eq_true.mpr fun i hi => by simp [v.ok.nosp i hi]

theorem update_nosp : NoSp (update v.callee) := by
  have : ((instrs (update v.callee)).all fun i => !Taint.clobbers i .rsp) = true := by
    rw [← Code.allInstrs_eq]
    simp only [update, Impl.MdStream.X86_64.update, Impl.MdStream.X86_64.updateBody,
      Impl.MdStream.X86_64.updateTail, Impl.MdStream.X86_64.compressAt, Code.allInstrs,
      v.callee_nosp, Bool.true_and]
    decide +kernel
  exact fun i hi => by simpa using List.all_eq_true.mp this i hi

theorem finalize_nosp : NoSp (finalize v.callee) := by
  have : ((instrs (finalize v.callee)).all fun i => !Taint.clobbers i .rsp) = true := by
    rw [← Code.allInstrs_eq]
    simp only [finalize, Impl.MdStream.X86_64.finalize, Impl.MdStream.X86_64.finalizeBody,
      Impl.MdStream.X86_64.compressAt, Code.allInstrs, v.callee_nosp, Bool.true_and]
    decide +kernel
  exact fun i hi => by simpa using List.all_eq_true.mp this i hi

end Compress

end VG.Proof.Sha1.X86_64
