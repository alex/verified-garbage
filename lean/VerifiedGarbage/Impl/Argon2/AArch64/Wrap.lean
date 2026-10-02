import VerifiedGarbage.Impl.Argon2.AArch64.Instructions
import VerifiedGarbage.TCB.AArch64.Isa

/-! # Wrap a reference-column sum with one masked subtraction

`x0` is the sum and `x1` the positive lane length. A sum below twice the
lane length needs at most one subtraction; the borrow mask selects the
original sum when it is already in range. No secret controls a branch.
-/

namespace VG.Impl.Argon2.AArch64.Wrap

open VG.AArch64
open VG.Impl.Argon2.AArch64.Instructions

def code : Prog isa := .block [mov .x6 .x0, sub .x0 .x1, sbb .x8, logic .eor .x6 .x0, logic .and .x6 .x8, logic .eor .x0 .x6].flatten

end VG.Impl.Argon2.AArch64.Wrap
