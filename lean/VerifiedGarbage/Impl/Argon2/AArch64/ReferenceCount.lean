import VerifiedGarbage.Impl.Argon2.AArch64.Instructions
import VerifiedGarbage.Impl.Argon2.AArch64.CountCandidates
import VerifiedGarbage.Impl.Argon2.AArch64.SelectWindow

/-! Compute both reference windows and select one without a secret branch.

`x0` and `x1` are the reference and current lanes. The pass and segment
position use CountCandidates' registers. `x4` receives the selected count.
-/

namespace VG.Impl.Argon2.AArch64.ReferenceCount

open VG VG.AArch64
open VG.Impl.Argon2.AArch64.Instructions

def code : Prog isa := .seq CountCandidates.code SelectWindow.code

end VG.Impl.Argon2.AArch64.ReferenceCount
