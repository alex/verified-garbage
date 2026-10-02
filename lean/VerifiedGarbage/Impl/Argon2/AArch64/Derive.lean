import VerifiedGarbage.Impl.Argon2.AArch64.InitialBody
import VerifiedGarbage.Impl.Argon2.AArch64.Parameters

/-! # ARM64 Argon2 entry point

Eight register arguments and ten caller stack arguments are copied into a
272-byte private frame. The first stack argument is a u32 followed by nine
64-bit values, so both AAPCS64 and Apple's ABI place the next argument at
offset eight. Every u32 argument is normalized before use. Seven saved
registers occupy 112 bytes; the original SP is 384 bytes above the frame.
-/
namespace VG.Impl.Argon2.AArch64.Derive
open VG VG.AArch64
open VG.Impl.Argon2.AArch64.Instructions

def saved : List Reg := [.x19, .x20, .x21, .x22, .x23, .x24, .x30]

def normalize (offset : Nat) : List Instr :=
  load .x8 .x19 offset ++ mov32 .x8 .x8 ++ store .x19 offset .x8

def setup : List Instr :=
  mov32 .x0 .x0 ++ mov32 .x5 .x5 ++ mov32 .x6 .x6 ++ mov32 .x7 .x7 ++
  [store .x19 72 .x5, store .x19 80 .x4, store .x19 88 .x3,
    store .x19 96 .x2, store .x19 104 .x1, store .x19 112 .x0,
    store .x19 176 .x6, store .x19 184 .x7, load .x24 .x19 248].flatten

def copyArg (j : Nat) : List Instr :=
  [.ldrSp .x8 (384 + 8 * j), .str .x .x8 .x19 (192 + 8 * j)]

def copyArgs : List Instr := (List.range 10).flatMap copyArg

def normalizeArgs : List Nat → Prog isa
  | [] => .block []
  | [d] => .block (normalize d)
  | d :: ds => .seq (.block (normalize d)) (normalizeArgs ds)

def prepareLocal : Prog isa := .seq (.block setup) (normalizeArgs [192])

def prepare : Prog isa :=
  .seq (.block [.addSp .x19 0]) (.seq (.block copyArgs) prepareLocal)

def frame (body : Prog isa) : List Reg → Prog isa
  | [] => .frame (.alloc 272) body (.free 272)
  | r :: rs => .frame (.push r) (frame body rs) (.pop r)

def body (name : String) (hash : HPrime.Hash) : Prog isa :=
  .seq prepare (.seq Parameters.code (InitialBody.code name hash))

def code (name : String) (hash : HPrime.Hash) : Prog isa := frame (body name hash) saved
end VG.Impl.Argon2.AArch64.Derive
