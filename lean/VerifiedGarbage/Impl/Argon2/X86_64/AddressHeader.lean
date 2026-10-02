import VerifiedGarbage.Impl.Argon2.X86_64.Compress

/-! Fill the first seven words of an independently generated address input.
The input pointer is `rdi`; its remaining words were cleared once. The frame
holds pass (0), address counter (8), passes (72), variant (112), blocks (240).
Lane and slice remain in `rbx` and `r14`. The counter is supplied after the
public address-generation loop advances it to its one-based value.
-/

namespace VG.Impl.Argon2.X86_64.AddressHeader

open VG.X86_64
open VG.Impl.Argon2.X86_64 (at_)

def registerWord (i : Nat) (r : Reg) : List Instr := [.store (at_ .rdi (8 * i)) r]

def frameWord (i offset : Nat) : List Instr :=
  [.mov .rax (.mem (at_ .rbp offset)), .store (at_ .rdi (8 * i)) .rax]

def frameOffset (i : Nat) : Nat :=
  if i = 0 then 0 else if i = 3 then 240 else if i = 4 then 72 else if i = 5 then 112 else 8

def field (i : Nat) : List Instr :=
  if i = 1 then registerWord i .rbx else if i = 2 then registerWord i .r14
  else frameWord i (frameOffset i)

def fields (n : Nat) : List Instr := (List.range n).flatMap field

def code : Prog isa := .block (fields 7)

end VG.Impl.Argon2.X86_64.AddressHeader
