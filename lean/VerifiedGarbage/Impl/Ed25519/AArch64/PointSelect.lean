import VerifiedGarbage.Impl.Ed25519.AArch64.FieldMemory

/-! Swap field elements under a mask, without secret-dependent branches. -/

namespace VG.Impl.Ed25519.AArch64

open VG.AArch64

def swapFields (ops : List (Slot × Slot)) : List Instr :=
  ops.flatMap fun (a, b) => cswap (offset a) (offset b)

end VG.Impl.Ed25519.AArch64
