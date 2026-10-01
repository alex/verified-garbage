import VerifiedGarbage.Impl.Ed25519.X86.CommonMemory
import VerifiedGarbage.Impl.Ed25519.X86.BitsExpand

namespace VG.Impl.Ed25519.X86
open VG.X86 VG.Impl.X25519.X86

def inputBits (i bytes : Nat) : List Instr :=
  [.mov .esi (.mem (at_ .esp (4 + 4 * i)))] ++ expandScalarBits bytes

end VG.Impl.Ed25519.X86
