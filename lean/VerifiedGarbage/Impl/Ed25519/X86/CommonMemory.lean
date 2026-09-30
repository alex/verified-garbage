import VerifiedGarbage.Impl.X25519.X86

namespace VG.Impl.Ed25519.X86
open VG.X86 VG.Impl.X25519.X86

def abiSave (scidx : Nat) : List Instr :=
  [.mov .eax (.mem (at_ .esp (4 + 4 * scidx))), .store (at_ .eax 0) .ebx,
    .store (at_ .eax 4) .esi, .store (at_ .eax 8) .edi, .store (at_ .eax 12) .ebp,
    .mov .edi (.reg .eax)]

def copyWords (dst n : Nat) : List Instr := (List.range n).flatMap fun k =>
  [.mov .eax (.mem (at_ .esi (4 * k))), .store (sc (dst + 4 * k)) .eax]

def outputWords (src n : Nat) : List Instr := (List.range n).flatMap fun k =>
  [.mov .eax (.mem (sc (src + 4 * k))), .store (at_ .esi (4 * k)) .eax]
end VG.Impl.Ed25519.X86
