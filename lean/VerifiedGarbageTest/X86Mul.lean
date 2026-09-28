import VerifiedGarbage.TCB.X86.Print

/-!
# Semantics tests for the x86 (32-bit) `mul`

Each expected value was computed on an x86-64 CPU running 32-bit code (a
static `i686-linux-gnu-gcc` build), by the same instruction (`mul ecx`, `mul
eax` or `mul edx` in inline assembly, reading EFLAGS with `pushfd` after
it), and is compared with the model's result on the same inputs. This tests
the transcription of the SDM's pseudocode (which half of the product goes
where, and when CF and OF are set), which review of the TCB would otherwise
have to catch by eye.
-/

namespace VG.Test.X86Mul

open X86

/-- A state with `a` in `eax`, `b` in `ecx` and `c` in `edx`, and every flag defined. -/
def s (a b c : BitVec 32) : State where
  gpr r := if r = .eax then a else if r = .ecx then b else if r = .edx then c else 7
  cf := some false
  zf := some true
  sf := some true
  of := some false
  mem _ := 0
  rd := []
  wr := []

/-- `eax`, `edx`, CF and OF after `mul src`, and whether SF and ZF are undefined. -/
def run (src : Reg) (a b c : BitVec 32) :
    Option (BitVec 32 × BitVec 32 × Option Bool × Option Bool × Bool) :=
  (exec (.mul src) (s a b c)).map fun t => (t.gpr .eax, t.gpr .edx, t.cf, t.of, t.sf.isNone && t.zf.isNone)

/-- `mul ecx` with `a` in `eax` and `b` in `ecx`: the expected low and high
halves and CF (= OF). -/
def ecx (a b lo hi : BitVec 32) (c : Bool) : Bool :=
  run .ecx a b 0 == some (lo, hi, some c, some c, true)

#guard ecx 0x0 0x0 0x0 0x0 false
#guard ecx 0x3 0x5 0xf 0x0 false
#guard ecx 0xffffffff 0x2 0xfffffffe 0x1 true
#guard ecx 0xffffffff 0xffffffff 0x1 0xfffffffe true
#guard ecx 0x12345678 0x9abcdef0 0x242d2080 0xb00ea4e true
#guard ecx 0x80000000 0x1 0x80000000 0x0 false
#guard ecx 0x3ffffff 0x3ffffff 0xf8000001 0xfffff true
#guard ecx 0xfffffff 0x10 0xfffffff0 0x0 false
#guard ecx 0x10000 0x10000 0x0 0x1 true

-- `mul eax` squares `eax`; `mul edx` multiplies by the old `edx`.
#guard run .eax 0xdeadbeef 0 0 == some (0x216da321, 0xc1b1cd12, some true, some true, true)
#guard run .edx 0x12345678 0 0x11112222 == some (0x14676bf0, 0x136b1a5, some true, some true, true)

-- Only `eax`, `edx` and the flags change.
#guard (exec (.mul .ecx) (s 3 5 9)).map (fun t => (t.gpr .ecx, t.gpr .ebx, t.gpr .esp, t.gpr .edi)) ==
  some (5, 7, 7, 7)

/-! ## Printing -/

#guard printer.instr (.mul .ecx) == ["mul ecx"]
#guard printer.instr (.mul .esi) == ["mul esi"]

-- `mul` is in the i486 baseline, and does not write `esp`.
#guard isa.requires (.mul .ecx) == []
#guard !isa.writesSp (.mul .esp)

end VG.Test.X86Mul
