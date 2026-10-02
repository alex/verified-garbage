import VerifiedGarbage.Impl.Argon2.X86_64.AddressHeader
import VerifiedGarbage.Impl.Argon2.X86_64.ClearBlock
import VerifiedGarbage.Spec.Argon2.Contract

/-! Independent-address generation in the shared 16 KiB scratch allocation.
G uses `[0,4096)`, temporary output `[4096,5120)`, input `[5120,6144)`,
address output `[6144,7168)`, and the zero block `[7168,8192)`. Every stage
reloads the scratch pointer from frame offset 248 after a compression call.
-/

namespace VG.Impl.Argon2.X86_64.AddressCalls

open VG.X86_64
open VG.Impl.Argon2.X86_64 (at_)

def pointer (offset : Nat) : List Instr := [
  .mov .rdi (.mem (at_ .rbp 248)), .alu .add .rdi (.imm (BitVec.ofNat 32 offset))]

def args (x y out : Nat) : List Instr := [
  .mov .rcx (.mem (at_ .rbp 248)),
  .mov .rdi (.reg .rcx), .alu .add .rdi (.imm (BitVec.ofNat 32 x)),
  .mov .rsi (.reg .rcx), .alu .add .rsi (.imm (BitVec.ofNat 32 y)),
  .mov .rdx (.reg .rcx), .alu .add .rdx (.imm (BitVec.ofNat 32 out))]

def stage (x y out : Nat) : Prog isa := .seq (.block (args x y out))
  (.call Spec.Argon2.compressApi.name VG.Impl.Argon2.X86_64.compress)

def calls : Prog isa := .seq (stage 7168 5120 4096) (stage 7168 4096 6144)

def clearAt (offset : Nat) : Prog isa := .seq (.block (pointer offset)) ClearBlock.code

def prepare : Prog isa := .seq (clearAt 5120) (.seq (clearAt 7168)
  (.seq (.block (pointer 5120)) AddressHeader.code))

def code : Prog isa := .seq prepare calls

end VG.Impl.Argon2.X86_64.AddressCalls
