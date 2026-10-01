import VerifiedGarbage.Impl.Argon2.X86_64.CountCandidates
import VerifiedGarbage.Impl.Argon2.X86_64.SelectWindow

/-! Compute both reference windows and select one without a secret branch.

`rdi` and `rsi` are the reference and current lanes. The pass and segment
position use CountCandidates' registers. `r8` receives the selected count.
-/

namespace VG.Impl.Argon2.X86_64.ReferenceCount

open VG VG.X86_64

def code : Prog isa := .seq CountCandidates.code SelectWindow.code

end VG.Impl.Argon2.X86_64.ReferenceCount
