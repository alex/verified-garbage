import VerifiedGarbage.Proof.Sha1.X86_64.Stream.Md

/-!
# Implementations of the SHA-1 compression function on x86-64

Untrusted: everything here is checked by Lean.

A `Compress` is what a function that calls the compression function needs
of it, so that its proof holds for every implementation: each is a variant
of the interface `Sha1Compress` on x86-64
(`Variants/Sha1Compress/X86_64/`), and each caller (in
`Generic/Sha1Compress/X86_64/`) is emitted once for each of them (see
`TCB/Emit.lean`).
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

end VG.Proof.Sha1.X86_64
