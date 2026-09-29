import VerifiedGarbage.TCB.X86_64.Print

/-!
# Semantics tests for the x86-64 `rorx` (BMI2) and `andn` (BMI1)

Each expected value was computed on an x86-64 CPU, by the same instruction
in inline assembly (`rorx r8d, edx, n`, whose destination held
`0xcccccccccccccccc`; `andn r32, r32, r32`, reading RFLAGS with `pushfq`
after it, with CF and OF set before it), and is compared with the model's
result on the same inputs. This tests the transcription of the SDM's
pseudocode (the rotation's direction, the zero extension of the 32-bit
result, which operand `andn` complements, and its flags), which review of the
TCB would otherwise have to catch by eye.
-/

namespace VG.Test.X86_64Bmi

open X86_64

/-- A state with `a` in `rdx`, `b` in `rcx`, `0xcccccccccccccccc` in every
other register, CF and OF set and ZF and SF clear. -/
def s (a b : BitVec 64) : State where
  gpr r := if r = .rdx then a else if r = .rcx then b else 0xcccccccccccccccc
  cf := some true
  zf := some false
  sf := some false
  of := some true
  mem _ := 0
  rd := []
  wr := []

/-- Whether `rorx r8d, edx, n` with `a` in `rdx` leaves `r` in `r8` and the
flags unchanged. -/
def rorx (a : BitVec 64) (n : Nat) (r : BitVec 64) : Bool :=
  (exec (.rorx32 .r8 .rdx n) (s a 0)).map (fun t => (t.gpr .r8, t.cf, t.zf, t.sf, t.of)) ==
    some (r, some true, some false, some false, some true)

#guard rorx 0x0 1 0x0
#guard rorx 0x0 7 0x0
#guard rorx 0x0 17 0x0
#guard rorx 0x0 25 0x0
#guard rorx 0x0 31 0x0
#guard rorx 0x1 1 0x80000000
#guard rorx 0x1 2 0x40000000
#guard rorx 0x1 11 0x200000
#guard rorx 0x1 19 0x2000
#guard rorx 0x1 31 0x2
#guard rorx 0xffffffffffffffff 1 0xffffffff
#guard rorx 0xffffffffffffffff 6 0xffffffff
#guard rorx 0xffffffffffffffff 13 0xffffffff
#guard rorx 0xffffffffffffffff 22 0xffffffff
#guard rorx 0xffffffffffffffff 31 0xffffffff
#guard rorx 0x6a09e667bb67ae85 1 0xddb3d742
#guard rorx 0x6a09e667bb67ae85 7 0xb76cf5d
#guard rorx 0x6a09e667bb67ae85 17 0xd742ddb3
#guard rorx 0x6a09e667bb67ae85 25 0xb3d742dd
#guard rorx 0x6a09e667bb67ae85 31 0x76cf5d0b
#guard rorx 0xdeadbeef80000001 1 0xc0000000
#guard rorx 0xdeadbeef80000001 2 0x60000000
#guard rorx 0xdeadbeef80000001 11 0x300000
#guard rorx 0xdeadbeef80000001 19 0x3000
#guard rorx 0xdeadbeef80000001 31 0x3
#guard rorx 0x510e527f 1 0xa887293f
#guard rorx 0x510e527f 6 0xfd443949
#guard rorx 0x510e527f 13 0x93fa8872
#guard rorx 0x510e527f 22 0x3949fd44
#guard rorx 0x510e527f 31 0xa21ca4fe

-- Counts outside `1 … 31` are not modelled.
#guard (exec (.rorx32 .r8 .rdx 0) (s 1 0)).isNone
#guard (exec (.rorx32 .r8 .rdx 32) (s 1 0)).isNone

/-- `r8`, CF, OF, ZF and SF after `andn r8d, edx, ecx`, with `a` in `rdx` and `b` in `rcx`. -/
def andn (a b : BitVec 64) : Option (BitVec 64 × Option Bool × Option Bool × Option Bool × Option Bool) :=
  (exec (.andn32 .r8 .rdx .rcx) (s a b)).map fun t => (t.gpr .r8, t.cf, t.of, t.zf, t.sf)

#guard andn 0x7fffffff 0x80000001 == some (0x80000000, some false, some false, some false, some true)
#guard andn 0x0 0x0 == some (0x0, some false, some false, some true, some false)
#guard andn 0xffffffff 0xffffffff == some (0x0, some false, some false, some true, some false)
#guard andn 0x9b05688c 0x1f83d9ab == some (0x4829123, some false, some false, some false, some false)
#guard andn 0x123456789abcdef0 0xfedcba9876543210 == some (0x64402000, some false, some false, some false, some false)
#guard andn 0x80000000 0xffffffff == some (0x7fffffff, some false, some false, some false, some false)
#guard andn 0xffffffffffffffff 0x0 == some (0x0, some false, some false, some true, some false)

-- Only the destination and the flags change.
#guard (exec (.andn32 .r8 .rdx .rcx) (s 3 5)).map (fun t => (t.gpr .rdx, t.gpr .rcx, t.gpr .rax)) ==
  some (3, 5, 0xcccccccccccccccc)
#guard (exec (.rorx32 .r8 .rdx 3) (s 3 5)).map (fun t => (t.gpr .rdx, t.gpr .rcx, t.gpr .rax)) ==
  some (3, 5, 0xcccccccccccccccc)

/-! ## Printing -/

#guard printer.instr (.rorx32 .r8 .rdx 6) == ["rorx r8d, edx, 6"]
#guard printer.instr (.rorx32 .rax .r15 31) == ["rorx eax, r15d, 31"]
#guard printer.instr (.andn32 .r8 .rdx .rcx) == ["andn r8d, edx, ecx"]

-- Their CPU features (the SDM's "CPUID Feature Flag"); neither writes `rsp`
-- unless it is the destination.
#guard isa.requires (.rorx32 .rax .rbx 2) == ["bmi2"]
#guard isa.requires (.andn32 .rax .rbx .rcx) == ["bmi1"]
#guard !isa.writesSp (.rorx32 .rax .rsp 2)
#guard isa.writesSp (.andn32 .rsp .rax .rbx)

end VG.Test.X86_64Bmi
