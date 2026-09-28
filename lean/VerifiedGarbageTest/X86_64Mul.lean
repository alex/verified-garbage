import VerifiedGarbage.TCB.X86_64.Print

/-!
# Semantics tests for the x86-64 `mul`

Each expected value was computed on an x86-64 CPU, by the same instruction
(`mul rcx`, `mul rax` or `mul rdx` in inline assembly, reading RFLAGS with
`pushfq` after it), and is compared with the model's result on the same
inputs. This tests the transcription of the SDM's pseudocode (which half of
the product goes where, and when CF and OF are set), which review of the TCB
would otherwise have to catch by eye.
-/

namespace VG.Test.X86_64Mul

open X86_64

/-- A state with `a` in `rax`, `b` in `rcx` and `c` in `rdx`, and every flag defined. -/
def s (a b c : BitVec 64) : State where
  gpr r := if r = .rax then a else if r = .rcx then b else if r = .rdx then c else 7
  cf := some false
  zf := some true
  sf := some true
  of := some false
  mem _ := 0
  rd := []
  wr := []

/-- `rax`, `rdx`, CF and OF after `mul src`, and whether SF and ZF are undefined. -/
def run (src : Reg) (a b c : BitVec 64) : Option (BitVec 64 × BitVec 64 × Option Bool × Option Bool × Bool) :=
  (exec (.mul src) (s a b c)).map fun t => (t.gpr .rax, t.gpr .rdx, t.cf, t.of, t.sf.isNone && t.zf.isNone)

/-- `mul rcx` with `a` in `rax` and `b` in `rcx`: the expected low and high
halves and CF (= OF). -/
def rcx (a b lo hi : BitVec 64) (c : Bool) : Bool :=
  run .rcx a b 0 == some (lo, hi, some c, some c, true)

#guard rcx 0x0 0x0 0x0 0x0 false
#guard rcx 0x3 0x5 0xf 0x0 false
#guard rcx 0xffffffffffffffff 0x2 0xfffffffffffffffe 0x1 true
#guard rcx 0xffffffffffffffff 0xffffffffffffffff 0x1 0xfffffffffffffffe true
#guard rcx 0x123456789abcdef 0xfedcba9876543210 0x2236d88fe5618cf0 0x121fa00ad77d742 true
#guard rcx 0x8000000000000000 0x1 0x8000000000000000 0x0 false
#guard rcx 0xffffffc0fffffff 0x100000000 0xfffffff00000000 0xffffffc true

-- `mul rax` squares `rax`; `mul rdx` multiplies by the old `rdx`.
#guard run .rax 0xdeadbeefcafebabe 0 0 ==
  some (0xb295b2eef140a504, 0xc1b1cd138292fa18, some true, some true, true)
#guard run .rdx 0x123456789abcdef0 0 0x1111222233334444 ==
  some (0x5e5af10d7f32f7c0, 0x136b1a5225c646c, some true, some true, true)

-- Only `rax`, `rdx` and the flags change.
#guard (exec (.mul .rcx) (s 3 5 9)).map (fun t => (t.gpr .rcx, t.gpr .rbx, t.gpr .r15)) == some (5, 7, 7)

/-! ## Printing -/

#guard printer.instr (.mul .rcx) == ["mul rcx"]
#guard printer.instr (.mul .r11) == ["mul r11"]

-- `mul` is in the x86-64 baseline, and does not write `rsp`.
#guard isa.requires (.mul .rcx) == []
#guard !isa.writesSp (.mul .rsp)

end VG.Test.X86_64Mul
