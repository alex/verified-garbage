import VerifiedGarbage.Impl.Argon2.X86_64.HPrime

/-!
# Argon2 H₀ initialization on x86-64

The enclosing derivation preserves its arguments in a stack frame. `rbp`
points to that frame and `rbx` to the 16 KiB scratch allocation. H₀ is
written to the first 64 frame bytes, followed by eight bytes reserved for
the column and lane prefixes used during memory initialization. Keeping
this input on the stack lets H′ use the entire scratch allocation under
its shared contract.

Every hash operation calls the supplied BLAKE2b streaming backend.
-/

namespace VG.Impl.Argon2.X86_64.Initial

open VG.X86_64
open VG.Impl.Argon2.X86_64.HPrime (Hash at_)

/-- Frame offsets for the register arguments, followed by the caller's
stack arguments. The enclosing frame occupies 168 bytes. -/
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
  [.mov .rax (.mem (at_ .rbp source)), .store32 (at_ .rbx destination) .rax]

/-- Lanes, tag length, requested memory, passes, version and variant. -/
def header : List Instr :=
  headerWord lanesOffset 768 ++ headerWord outLenOffset 772 ++
  headerWord memoryCostOffset 776 ++ headerWord passOffset 780 ++
  ([.mov32 .rax (.imm 0x13), .store32 (at_ .rbx 784) .rax] : List Instr) ++
  headerWord kindOffset 788

def start (h : Hash) : Prog isa :=
  .seq (.block [.mov32 .rsi (.imm 64)])
  (.seq (HPrime.init h)
  (.seq (.block header)
  (.seq (HPrime.absorbFixed h 768 24)
    (.block [.mov32 .r12 (.imm 24)]))))

/-- Prefix the next input's length, with the running byte count in `r12`.
The length stays in a callee-saved register across both update calls. -/
def lengthArgs (offset : Nat) : List Instr :=
  [.mov .r14 (.mem (at_ .rbp offset)), .store32 (at_ .rbx 792) .r14,
    .mov .rsi (.reg .r12), .mov .rdx (.reg .rbx), .alu .add .rdx (.imm 792),
    .mov32 .rcx (.imm 4)]

def inputArgs (offset : Nat) : List Instr :=
  [.alu .add .r12 (.imm 4), .mov .rsi (.reg .r12),
    .mov .rdx (.mem (at_ .rbp offset)), .mov .rcx (.reg .r14)]

/-- Append LE32(length) and then the complete input, including empty inputs. -/
def absorb (h : Hash) (pointerOffset lengthOffset : Nat) : Prog isa :=
  .seq (.block (lengthArgs lengthOffset))
  (.seq (HPrime.update h)
  (.seq (.block (inputArgs pointerOffset))
  (.seq (HPrime.update h)
    (.block [.alu .add .r12 (.reg .r14)]))))

def finishArgs : List Instr :=
  [.mov .rdi (.reg .rbx), .mov .rsi (.reg .r12), .mov .rdx (.reg .rbp),
    .mov .rcx (.reg .rbx), .alu .add .rcx (.imm 192)]

/-- H₀ of the four byte-string inputs and the public Argon2 parameters. -/
def code (h : Hash) : Prog isa :=
  .seq (start h)
  (.seq (absorb h passwordOffset passwordLenOffset)
  (.seq (absorb h saltOffset saltLenOffset)
  (.seq (absorb h secretOffset secretLenOffset)
  (.seq (absorb h adOffset adLenOffset)
  (.seq (.block finishArgs) (.call h.finalizeName h.finalize))))))

end VG.Impl.Argon2.X86_64.Initial
