import VerifiedGarbage.Impl.Argon2.X86_64.AddressCalls

/-! Cache one address block per 128 segment positions. Frame offset eight holds
its one-based counter; initializing it to zero forces generation even when the
first filled index is two. Only public counters control regeneration.
-/

namespace VG.Impl.Argon2.X86_64.AddressCache

open VG.X86_64
open VG.Impl.Argon2.X86_64 (at_)

def check : List Instr := [
  .mov .rax (.reg .r15), .shift .shr .rax 7, .alu .add .rax (.imm 1),
  .alu .cmp .rax (.mem (at_ .rbp 8))]

def save : List Instr := [.store (at_ .rbp 8) .rax]

def select : Prog isa := .seq (.block check)
  (.ite .e (.block []) (.seq (.block save) AddressCalls.code))

def wordArgs : List Instr := [
  .mov .rcx (.mem (at_ .rbp 248)), .mov .rax (.reg .r15), .alu .and .rax (.imm 127)]

def wordRead : List Instr := [
  .mov .rdi (.mem { base := .rcx, index := some .rax, scale := 8, disp := 6144 })]

def word : Prog isa := .seq (.block wordArgs) (.block wordRead)

def code : Prog isa := .seq select word

end VG.Impl.Argon2.X86_64.AddressCache
