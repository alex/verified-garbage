import VerifiedGarbage.Spec.Sha1
import VerifiedGarbage.TCB.AArch64.Isa

/-!
# SHA-1 compression with AArch64 SHA instructions

ABCD lives in v0 and E in the low word of v1. v4–v7 hold the rolling
sixteen-word schedule. Each group executes four rounds with SHA1C/P/M,
using SHA1H to retain the next E before overwriting ABCD. Only caller-saved
registers are used. Scratch is unused; all addresses and branches are public.
-/

namespace VG.Impl.Sha1.AArch64.Sha2

open VG.AArch64
open VG.Spec.Sha1 (K)

def msg (i : Nat) : VReg := [.v4, .v5, .v6, .v7].getD (i % 4) .v4

def op (i : Nat) : Sha1Op :=
  if i < 5 then .c else if i < 10 then .p else if i < 15 then .m else .p

def schedule (i : Nat) : List Instr :=
  if i < 4 then
    [.ldrq (msg i) .x1 (16 * i), .vop (.rev .rev32b (msg i) (msg i))]
  else
    [.vop (.sha1su0 (msg i) (msg (i + 1)) (msg (i + 2))),
     .vop (.sha1su1 (msg i) (msg (i + 3)))]

def rounds4 (i : Nat) : List Instr :=
  [.movz .w .x4 ((K (4 * i)).extractLsb' 0 16) 0,
   .movk .w .x4 ((K (4 * i)).extractLsb' 16 16) 1,
   .vop (.dup .s4 .v3 .x4),
   .vop (.add .s4 .v3 .v3 (msg i)),
   .vop (.sha1h .v2 .v0),
   .vop (.sha1 (op i) .v0 .v1 .v3),
   .vop (.mov .v1 .v2)]

def rounds : Nat → Prog isa
  | 0 => .block []
  | n + 1 => .seq (rounds n) (.block (schedule n ++ rounds4 n))

def load : List Instr :=
  [.ldrq .v0 .x0 0, .ldr .w .x4 .x0 16,
   .vop (.dup .s4 .v1 .x4), .vop (.dupS .v1 .v1 0),
   .vop (.mov .v16 .v0), .vop (.mov .v17 .v1)]

def store : List Instr :=
  [.vop (.add .s4 .v0 .v0 .v16), .vop (.add .s4 .v1 .v1 .v17),
   .strq .v0 .x0 0, .umov .w .x4 .v1 0, .str .w .x4 .x0 16,
   .addImm .x .x1 .x1 64, .subImm .x .x2 .x2 1]

def body : Prog isa := .seq (.block load) (.seq (rounds 20) (.block store))

def compress : Prog isa :=
  .ite (.zero .x .x2) (.block []) (.loop body (.nonzero .x .x2))

end VG.Impl.Sha1.AArch64.Sha2
