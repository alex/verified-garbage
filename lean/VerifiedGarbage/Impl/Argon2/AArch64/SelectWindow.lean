import VerifiedGarbage.Impl.Argon2.AArch64.Instructions
import VerifiedGarbage.TCB.AArch64.Isa

/-! # Select the eligible window without branching on the reference lane

`rdi,rsi` are the reference and current lanes; `rdx,rcx` hold the same-lane
and cross-lane window lengths. `x4` receives the selected length. Subtracting
one from the lanes' XOR borrows exactly when the lanes match, supplying the
mask for the selection. The counts may be secret too.
-/

namespace VG.Impl.Argon2.AArch64.SelectWindow

open VG.AArch64
open VG.Impl.Argon2.AArch64.Instructions

def code : Prog isa := .block [mov .x8 .x0, logic .eor .x8 .x1, subi .x8 1, sbb .x8, mov .x4 .x3, logic .eor .x2 .x3, logic .and .x2 .x8, logic .eor .x4 .x2].flatten

end VG.Impl.Argon2.AArch64.SelectWindow
