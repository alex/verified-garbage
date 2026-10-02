import VerifiedGarbage.Impl.Argon2.X86_64.InitialBody
import VerifiedGarbage.Impl.Argon2.X86_64.Parameters

/-! The complete System V entry point, including u32 argument normalization. -/

namespace VG.Impl.Argon2.X86_64.Derive

open VG VG.X86_64
open VG.Impl.Argon2.X86_64.HPrime (at_)

def saved : List Reg := [.rbx, .rbp, .r12, .r13, .r14, .r15]

def normalize (offset : Nat) : List Instr :=
  [.mov .rax (.mem (at_ .rbp offset)), .mov32 .rax (.reg .rax), .store (at_ .rbp offset) .rax]

def setup : List Instr :=
  [.mov .rbp (.reg .rsp), .mov32 .rdi (.reg .rdi), .mov32 .r9 (.reg .r9),
    .store (at_ .rbp 72) .r9, .store (at_ .rbp 80) .r8,
    .store (at_ .rbp 88) .rcx, .store (at_ .rbp 96) .rdx,
    .store (at_ .rbp 104) .rsi, .store (at_ .rbp 112) .rdi,
    .mov .rbx (.mem (at_ .rbp 248))]

def normalizeArgs : List Nat → Prog isa
  | [] => .block []
  | [d] => .block (normalize d)
  | d :: e :: ds => .seq (.block (normalize d)) (normalizeArgs (e :: ds))

def prepare : Prog isa := .seq (.block setup) (normalizeArgs [176, 184, 192])

/-- One nested frame per saved register restores every register separately.
The inner fifteen words reserve the 120-byte local argument/hash frame. -/
def frame (body : Prog isa) : List Reg → Prog isa
  | [] => .frame (.push (List.replicate 15 .rax)) body (.pop .rax 15)
  | r :: rs => .frame (.push [r]) (frame body rs) (.pop r 1)

def body (name : String) (hash : HPrime.Hash) : Prog isa :=
  .seq prepare (.seq Parameters.code (InitialBody.code name hash))

def code (name : String) (hash : HPrime.Hash) : Prog isa := frame (body name hash) saved

end VG.Impl.Argon2.X86_64.Derive
