import VerifiedGarbage.Proof.Sha512.X86_64.Stream.Md

/-!
# Implementations of the SHA-512 compression function on x86-64

A `Compress` is what a function that calls the compression function needs
of it, so that its proof holds for every implementation: each makes each
member of the SHA-512 family a variant of the interface `MdHash` on x86-64
(`Variants/MdHash/X86_64/Sha384*.lean`, …,
`Proof/Pbkdf2/Md/X86_64/Hashes/Sha512.lean`), and each function built on it
(in `Generic/MdHash/X86_64/`) is emitted once for each of them (see
`TCB/Emit.lean`). The four members share the implementations, so they are
here: `scalar`, `avx2` and `shani`.
-/

namespace VG.Proof.Sha512.X86_64

open VG.X86_64

/-- An implementation of the SHA-512 compression function on x86-64. -/
structure Compress where
  /-- Its symbol and code. -/
  callee : Impl.Sha512.X86_64.Stream.Callee
  /-- It is correct and constant time, and keeps what callers need. -/
  ok : MdStream.X86_64.CalleeOk (P := Stream.params) md callee.code
  /-- It never loads MXCSR. -/
  mxcsr : callee.code.allInstrs (fun i => !loadsMxcsr i) = true
  /-- It never writes the stack pointer. -/
  spSafe : callee.code.all (fun i => !isa.writesSp i) = true
  /-- What the names of its callers' instances end with (e.g. `_avx2`;
  nothing for the baseline implementation). -/
  suffix : String
  /-- The CPU features its code requires, which its callers require too. -/
  features : List String

namespace Compress

/-- The scalar implementation, `vg_sha512_compress`, in the baseline ISA. -/
def scalar : Compress where
  callee := .scalar
  ok := Stream.scalar_ok
  mxcsr := by change Impl.Sha512.X86_64.compress.allInstrs _ = true; lit_decide
  spSafe := Code.all_of_allInstrs (by change Impl.Sha512.X86_64.compress.allInstrs _ = true; lit_decide)
  suffix := ""
  features := []

/-- `vg_sha512_compress_avx2`, which needs AVX, AVX2, BMI1 and BMI2. -/
def avx2 : Compress where
  callee := .avx2
  ok := Stream.avx2_ok
  mxcsr := by change Impl.Sha512.X86_64.Avx2.compress.allInstrs _ = true; lit_decide
  spSafe := Code.all_of_allInstrs (by change Impl.Sha512.X86_64.Avx2.compress.allInstrs _ = true; lit_decide)
  suffix := "_avx2"
  features := ["avx", "avx2", "bmi1", "bmi2"]

/-- `vg_sha512_compress_shani`, which needs the SHA512 extension, AVX and AVX2. -/
def shani : Compress where
  callee := .shani
  ok := Stream.shani_ok
  mxcsr := by change Impl.Sha512.X86_64.ShaNi.compress.allInstrs _ = true; lit_decide
  spSafe := Code.all_of_allInstrs (by change Impl.Sha512.X86_64.ShaNi.compress.allInstrs _ = true; lit_decide)
  suffix := "_shani"
  features := ["avx", "avx2", "sha512"]

end Compress

end VG.Proof.Sha512.X86_64
