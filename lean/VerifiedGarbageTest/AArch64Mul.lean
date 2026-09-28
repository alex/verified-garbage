import VerifiedGarbage.TCB.AArch64.Print

/-!
# Semantics tests for the AArch64 `madd`, `mul` and `lsl`

Each expected value was computed by the same instruction (`madd`, `mul` or
`lsl`, 32- and 64-bit, in inline assembly, with the destination holding
`0xdeadbeefdeadbeef` beforehand so that the zero-extension of a 32-bit
result shows) in a program cross-compiled with `aarch64-linux-gnu-gcc` and
run under `qemu-aarch64`'s emulation of an AArch64 CPU, not on Arm hardware,
and is compared with the model's result on the same inputs. This tests the
transcription of the Arm ARM's pseudocode (the operand order of MADD, and
the truncation and zero-extension of a result at the operand size), which
review of the TCB would otherwise have to catch by eye.
-/

namespace VG.Test.AArch64Mul

open AArch64

/-- A state with `n` in `x1`, `m` in `x2`, `a` in `x3`, and
`0xdeadbeefdeadbeef` in `x0` and every other register. -/
def s (n m a : BitVec 64) : State where
  gpr r := if r = .x1 then n else if r = .x2 then m else if r = .x3 then a else 0xdeadbeefdeadbeef
  sp := 0x1000
  mem _ := 0
  rd := []
  wr := []

/-- `x0` after the instruction `i`. -/
def run (i : Instr) (n m a : BitVec 64) : Option (BitVec 64) :=
  (exec i (s n m a)).map (·.gpr .x0)

/-- `madd x0, x1, x2, x3`, `madd w0, w1, w2, w3`, `mul x0, x1, x2` and `mul
w0, w1, w2`: the expected values of `x0`. -/
def madd (n m a maddX maddW mulX mulW : BitVec 64) : Bool :=
  run (.madd .x .x0 .x1 .x2 .x3) n m a == some maddX &&
  run (.madd .w .x0 .x1 .x2 .x3) n m a == some maddW &&
  run (.mul .x .x0 .x1 .x2) n m a == some mulX &&
  run (.mul .w .x0 .x1 .x2) n m a == some mulW

#guard madd 0x0 0x0 0x0 0x0 0x0 0x0 0x0
#guard madd 0x3 0x5 0x7 0x16 0x16 0xf 0xf
#guard madd 0xffffffffffffffff 0xffffffffffffffff 0x0 0x1 0x1 0x1 0x1
#guard madd 0xffffffffffffffff 0xffffffffffffffff 0xffffffffffffffff 0x0 0x0 0x1 0x1
#guard madd 0x123456789abcdef 0xfedcba9876543210 0x1111222233334444
  0x3347fab21894d134 0x1894d134 0x2236d88fe5618cf0 0xe5618cf0
#guard madd 0x3ffffff 0x3ffffff 0x3ffffff 0xffffffc000000 0xfc000000 0xffffff8000001 0xf8000001
#guard madd 0xdeadbeefcafebabe 0x123456789abcdef 0x8000000000000000
  0xfeb689f4ea447d62 0xea447d62 0x7eb689f4ea447d62 0xea447d62
-- A 32-bit form reads only the low halves of its sources.
#guard madd 0xffffffff00000002 0x1234567800000003 0xabcdef0000000005
  0xd0369bed0000000b 0xb 0x2468aced00000006 0x6

-- The destination is also a source: `madd x3, x1, x2, x3`, and `madd x3, x3,
-- x3, x3`, `mul x3, x3, x3`, `mul w3, w3, w3`.
#guard (exec (.madd .x .x3 .x1 .x2 .x3) (s 3 5 0xffffffffffffffff)).map (·.gpr .x3) == some 0xe
#guard (exec (.madd .x .x3 .x3 .x3 .x3) (s 0 0 0xdeadbeefcafebabe)).map (·.gpr .x3) ==
  some 0x914371debc3f5fc2
#guard (exec (.mul .x .x3 .x3 .x3) (s 0 0 0xdeadbeefcafebabe)).map (·.gpr .x3) ==
  some 0xb295b2eef140a504
#guard (exec (.mul .w .x3 .x3 .x3) (s 0 0 0xdeadbeefcafebabe)).map (·.gpr .x3) == some 0xf140a504

/-- `lsl x0, x1, #sh` and `lsl w0, w1, #sh`: the expected values of `x0`. -/
def lsl (n : BitVec 64) (sh : Nat) (x w : BitVec 64) : Bool :=
  run (.lsl .x .x0 .x1 sh) n 0 0 == some x && run (.lsl .w .x0 .x1 sh) n 0 0 == some w

#guard lsl 0xdeadbeefcafebabe 0 0xdeadbeefcafebabe 0xcafebabe
#guard lsl 0xdeadbeefcafebabe 1 0xbd5b7ddf95fd757c 0x95fd757c
#guard lsl 0xdeadbeefcafebabe 26 0xbf2bfaeaf8000000 0xf8000000
#guard lsl 0xffffffffffffffff 0 0xffffffffffffffff 0xffffffff
#guard lsl 0xffffffffffffffff 1 0xfffffffffffffffe 0xfffffffe
#guard lsl 0xffffffffffffffff 26 0xfffffffffc000000 0xfc000000
#guard lsl 0x1 1 0x2 0x2
#guard lsl 0x1 26 0x4000000 0x4000000
#guard run (.lsl .x .x0 .x1 63) 0xdeadbeefcafebabe 0 0 == some 0x0
#guard run (.lsl .x .x0 .x1 63) 0xffffffffffffffff 0 0 == some 0x8000000000000000
#guard run (.lsl .x .x0 .x1 63) 0x1 0 0 == some 0x8000000000000000
#guard run (.lsl .w .x0 .x1 31) 0xdeadbeefcafebabe 0 0 == some 0x0
#guard run (.lsl .w .x0 .x1 31) 0xffffffffffffffff 0 0 == some 0x80000000
#guard run (.lsl .w .x0 .x1 31) 0x1 0 0 == some 0x80000000

-- A shift by the operand size or more cannot be encoded.
#guard run (.lsl .x .x0 .x1 64) 1 0 0 == none
#guard run (.lsl .w .x0 .x1 32) 1 0 0 == none

-- Only the destination changes.
#guard (exec (.madd .x .x0 .x1 .x2 .x3) (s 3 5 7)).map
  (fun t => (t.gpr .x1, t.gpr .x2, t.gpr .x3, t.gpr .x4, t.sp)) ==
  some (3, 5, 7, 0xdeadbeefdeadbeef, 0x1000)

/-! ## Printing -/

#guard printer.instr (.madd .x .x0 .x1 .x2 .x3) == ["madd x0, x1, x2, x3"]
#guard printer.instr (.madd .w .x4 .x5 .x6 .x30) == ["madd w4, w5, w6, w30"]
#guard printer.instr (.mul .x .x0 .x1 .x2) == ["mul x0, x1, x2"]
#guard printer.instr (.mul .w .x19 .x20 .x21) == ["mul w19, w20, w21"]
#guard printer.instr (.lsl .x .x0 .x1 26) == ["lsl x0, x1, #26"]
#guard printer.instr (.lsl .w .x0 .x1 31) == ["lsl w0, w1, #31"]

-- In the ARMv8.0-A baseline.
#guard isa.requires (.madd .x .x0 .x1 .x2 .x3) == []
#guard isa.requires (.mul .x .x0 .x1 .x2) == []
#guard isa.requires (.lsl .x .x0 .x1 1) == []

end VG.Test.AArch64Mul
