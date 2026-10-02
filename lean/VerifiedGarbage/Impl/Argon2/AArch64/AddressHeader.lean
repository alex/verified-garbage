import VerifiedGarbage.Impl.Argon2.AArch64.Instructions
import VerifiedGarbage.Impl.Argon2.AArch64.Compress

/-! Fill the first seven words of an independently generated address input.
The input pointer is `x0`; its remaining words were cleared once. The frame
holds pass (0), address counter (8), passes (72), variant (112), blocks (240).
Lane and slice remain in `x24` and `x22`. The counter is supplied after the
public address-generation loop advances it to its one-based value.
-/

namespace VG.Impl.Argon2.AArch64.AddressHeader

open VG.AArch64
open VG.Impl.Argon2.AArch64.Instructions

def registerWord (i : Nat) (r : Reg) : List Instr := [store .x0 (8 * i) r].flatten

def frameWord (i offset : Nat) : List Instr :=
  [load .x8 .x19 offset, store .x0 (8 * i) .x8].flatten

def frameOffset (i : Nat) : Nat :=
  if i = 0 then 0 else if i = 3 then 240 else if i = 4 then 72 else if i = 5 then 112 else 8

def field (i : Nat) : List Instr :=
  if i = 1 then registerWord i .x24 else if i = 2 then registerWord i .x22
  else frameWord i (frameOffset i)

def fields (n : Nat) : List Instr := (List.range n).flatMap field

def code : Prog isa := .block (fields 7)

end VG.Impl.Argon2.AArch64.AddressHeader
