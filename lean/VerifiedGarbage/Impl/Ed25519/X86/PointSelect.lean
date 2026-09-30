import VerifiedGarbage.Impl.Ed25519.X86.FieldMemory

/-! Select the saved point with a full-word mask in ecx. -/
namespace VG.Impl.Ed25519.X86
open VG.X86

def swapFields (pairs : List (Slot × Slot)) : List Instr :=
  pairs.flatMap fun (a, b) => VG.Impl.X25519.X86.cswap (offset a) (offset b)

def pointSelect : List Instr := swapFields [(0, 17), (1, 18), (2, 19), (3, 20)]

end VG.Impl.Ed25519.X86
