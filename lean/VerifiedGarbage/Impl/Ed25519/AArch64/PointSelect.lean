import VerifiedGarbage.Impl.Ed25519.AArch64.FieldMemory

/-! Select the saved point with a mask, without secret-dependent branches. -/

namespace VG.Impl.Ed25519.AArch64

open VG.AArch64

def swapFields (ops : List (Slot × Slot)) : List Instr :=
  ops.flatMap fun (a, b) => cswap (offset a) (offset b)

def pointSelectPairs : List (Slot × Slot) := [(0, 17), (1, 18), (2, 19), (3, 20)]

/-- x3 is all ones to restore the saved point, zero to retain the current point. -/
def pointSelect : List Instr := swapFields pointSelectPairs

end VG.Impl.Ed25519.AArch64
