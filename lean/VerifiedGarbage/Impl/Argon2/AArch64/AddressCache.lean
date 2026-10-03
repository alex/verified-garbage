import VerifiedGarbage.Impl.Argon2.AArch64.Instructions
import VerifiedGarbage.Impl.Argon2.AArch64.AddressCalls

/-! Cache one address block per 128 segment positions. Frame offset eight holds
its one-based counter; initializing it to zero forces generation even when the
first filled index is two. Only public counters control regeneration.
-/

namespace VG.Impl.Argon2.AArch64.AddressCache

open VG.AArch64
open VG.Impl.Argon2.AArch64.Instructions

def check : List Instr := [mov .x8 .x23, shr .x8 7, addi .x8 1, comparem .x8 .x19 8].flatten

def save : List Instr := [store .x19 8 .x8].flatten

def select : Prog isa := .seq (.block check)
  (.ite (.zero .x .x15) (.block []) (.seq (.block save) AddressCalls.code))

def wordArgs : List Instr := [load .x3 .x19 248, mov .x8 .x23, logici .and .x8 127].flatten

def wordRead : List Instr := [mov .x13 .x8, add .x13 .x13, add .x13 .x13, add .x13 .x13, add .x13 .x3, addi .x13 6144, load .x0 .x13 0].flatten

def word : Prog isa := .seq (.block wordArgs) (.block wordRead)

def code : Prog isa := .seq select word

end VG.Impl.Argon2.AArch64.AddressCache
