import VerifiedGarbage.Impl.Ed25519.X86.Whole.Setup

namespace VG.Impl.Ed25519.X86.Whole
/-- Clear consecutive 32-bit frame words, starting at word index `start`. -/
def zeroWords (start count : Nat) : List VG.X86.Instr :=
  setup start (List.replicate count (.const 0))
end VG.Impl.Ed25519.X86.Whole
