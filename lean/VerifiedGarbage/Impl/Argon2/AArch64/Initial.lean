import VerifiedGarbage.Impl.Argon2.AArch64.Instructions
import VerifiedGarbage.Impl.Argon2.AArch64.HPrime

/-!
# Argon2 H₀ initialization on ARM64

The enclosing derivation preserves its arguments in a stack frame. `x19`
points to that frame and `x24` to the 16 KiB scratch allocation. H₀ is
written to the first 64 frame bytes, followed by eight bytes reserved for
the column and lane prefixes used during memory initialization. Keeping
this input on the stack lets H′ use the entire scratch allocation under
its shared contract.

Every hash operation calls the supplied BLAKE2b streaming backend.
-/

namespace VG.Impl.Argon2.AArch64.Initial

open VG.AArch64
open VG.Impl.Argon2.AArch64.Instructions
open VG.Impl.Argon2.AArch64.HPrime (Hash)

/-- Frame offsets for the saved register arguments and private copies of
the caller's stack arguments. The private frame occupies 272 bytes. -/
def passOffset : Nat := 72
def saltLenOffset : Nat := 80
def saltOffset : Nat := 88
def passwordLenOffset : Nat := 96
def passwordOffset : Nat := 104
def kindOffset : Nat := 112
def memoryCostOffset : Nat := 176
def lanesOffset : Nat := 184
def secretOffset : Nat := 200
def secretLenOffset : Nat := 208
def adOffset : Nat := 216
def adLenOffset : Nat := 224
def outLenOffset : Nat := 264

/-- Copy a public parameter's low 32 bits into the H₀ header. -/
def headerWord (source destination : Nat) : List Instr :=
  [load .x8 .x19 source, store32 .x24 destination .x8].flatten

def headerSource (j : Nat) : Nat :=
  if j = 0 then lanesOffset else if j = 1 then outLenOffset else
  if j = 2 then memoryCostOffset else if j = 3 then passOffset else kindOffset

/-- One public parameter, or the fixed version word, in the H₀ header. -/
def headerSlot (j : Nat) : List Instr :=
  if j = 4 then
    [imm .x8 0x13, store32 .x24 (768 + 4 * j) .x8].flatten
  else headerWord (headerSource j) (768 + 4 * j)

/-- Lanes, tag length, requested memory, passes, version and variant. -/
def header : List Instr := (List.range 6).flatMap headerSlot

def headerCode : Prog isa := .block header

def start (h : Hash) : Prog isa :=
  .seq (.block [imm .x1 64].flatten)
  (.seq (HPrime.init h)
  (.seq headerCode
  (.seq (HPrime.absorbFixed h 768 24)
    (.block [imm .x20 24].flatten))))

/-- Prefix the next input's length, with the running byte count in `x20`.
The length stays in a callee-saved register across both update calls. -/
def lengthArgs (offset : Nat) : List Instr :=
  [load .x22 .x19 offset, store32 .x24 792 .x22, mov .x1 .x20, mov .x2 .x24, addi .x2 792, imm .x3 4].flatten

def inputArgs (offset : Nat) : List Instr :=
  [addi .x20 4, mov .x1 .x20, load .x2 .x19 offset, mov .x3 .x22].flatten

/-- Append LE32(length) and then the complete input, including empty inputs. -/
def absorb (h : Hash) (pointerOffset lengthOffset : Nat) : Prog isa :=
  .seq (.block (lengthArgs lengthOffset))
  (.seq (HPrime.update h)
  (.seq (.block (inputArgs pointerOffset))
  (.seq (HPrime.update h)
    (.block [add .x20 .x22].flatten))))

/-- Finalize in hash scratch, then copy H₀ into the memory-initialization input. -/
def finish (h : Hash) : Prog isa :=
  .seq (.block [mov .x1 .x20].flatten)
  (.seq (HPrime.finalize h)
  (.seq (.block [mov .x22 .x19, imm .x8 64].flatten) HPrime.copy))

/-- H₀ of the four byte-string inputs and the public Argon2 parameters. -/
def code (h : Hash) : Prog isa :=
  .seq (start h)
  (.seq (absorb h passwordOffset passwordLenOffset)
  (.seq (absorb h saltOffset saltLenOffset)
  (.seq (absorb h secretOffset secretLenOffset)
  (.seq (absorb h adOffset adLenOffset)
  (finish h)))))

end VG.Impl.Argon2.AArch64.Initial
