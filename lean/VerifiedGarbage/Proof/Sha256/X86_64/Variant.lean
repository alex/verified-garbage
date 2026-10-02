import VerifiedGarbage.Proof.Sha256.X86_64.Stream.Common

/-!
# Implementations of the SHA-256 compression function on x86-64

A `Compress` is what a function that calls the compression function needs
of it, so that its proof holds for every implementation: each makes
SHA-256 a variant of the interface `MdHash` on x86-64
(`Variants/MdHash/X86_64/Sha256*.lean`, `Proof/Pbkdf2/Md/X86_64/Hashes/Sha256.lean`),
and each function built on it (in `Generic/MdHash/X86_64/`) is emitted once
for each of them (see `TCB/Emit.lean`).
-/

namespace VG.Proof.Sha256.X86_64

open VG.X86_64

/-- An implementation of the SHA-256 compression function on x86-64. -/
structure Compress where
  /-- Its symbol and code. -/
  callee : Impl.Sha256.X86_64.Stream.Callee
  /-- It is correct and constant time, and keeps what callers need. -/
  ok : callee.Ok
  /-- It never loads MXCSR. -/
  mxcsr : callee.code.allInstrs (fun i => !loadsMxcsr i) = true
  /-- It never writes the stack pointer. -/
  spSafe : callee.code.all (fun i => !isa.writesSp i) = true
  /-- What the names of its callers' instances end with (e.g. `_shani`;
  nothing for the baseline implementation). -/
  suffix : String
  /-- The CPU features its code requires, which its callers require too. -/
  features : List String

end VG.Proof.Sha256.X86_64
