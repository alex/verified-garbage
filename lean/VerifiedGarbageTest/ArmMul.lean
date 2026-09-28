import VerifiedGarbage.TCB.Arm.Print

/-!
# Semantics tests for the ARMv7 `mul`

Each expected value was computed by the same instruction (`mul d, n, m`, and
`mul d, d, m`, in inline assembly, with the destination holding `0xdeadbeef`
beforehand) in a program cross-compiled with `arm-linux-gnueabihf-gcc
-march=armv7-a`, both as ARM and as Thumb (where the assembler picks the
32-bit `mul.w`), and run under `qemu-arm`'s emulation of an ARMv7 CPU, not
on Arm hardware; both gave the same results. They are compared with the
model's result on the same inputs. The same program read the flags after
`cmp n, n; mul d, n, m`: `mul` left them as `cmp` set them.
-/

namespace VG.Test.ArmMul

open Arm

/-- A state with `n` in `r1`, `m` in `r2`, and `0xdeadbeef` in every other
register, with the flags `N = 0, Z = 1, C = 1, V = 0` (as `cmp` of a
register with itself sets them). -/
def s (n m : BitVec 32) : State where
  gpr r := if r = .r1 then n else if r = .r2 then m else 0xdeadbeef
  sp := 0x1000
  n := false
  z := true
  c := true
  v := false
  mem _ := 0
  rd := []
  wr := []

/-- `mul r0, r1, r2` and `mul r1, r1, r2`: the expected results. -/
def mul (n m d dd : BitVec 32) : Bool :=
  (exec (.mul .r0 .r1 .r2) (s n m)).map (·.gpr .r0) == some d &&
  (exec (.mul .r1 .r1 .r2) (s n m)).map (·.gpr .r1) == some dd

#guard mul 0x0 0x0 0x0 0x0
#guard mul 0x3 0x5 0xf 0xf
#guard mul 0xffffffff 0xffffffff 0x1 0x1
#guard mul 0x3ffffff 0x3ffffff 0xf8000001 0xf8000001
#guard mul 0x12345678 0x9abcdef0 0x242d2080 0x242d2080
#guard mul 0x80000000 0x2 0x0 0x0
#guard mul 0xdeadbeef 0xcafebabe 0x88cf5b62 0x88cf5b62
#guard mul 0x1fff 0x1fff 0x3ffc001 0x3ffc001
#guard mul 0xffffffff 0x1 0xffffffff 0xffffffff
#guard mul 0x10000 0x10000 0x0 0x0

-- The flags are unchanged (as the program saw), and so is every other register.
#guard (exec (.mul .r0 .r1 .r2) (s 0xffffffff 0xffffffff)).map
  (fun t => (t.n, t.z, t.c, t.v)) == some (false, true, true, false)
#guard (exec (.mul .r0 .r1 .r2) (s 7 9)).map (fun t => (t.gpr .r1, t.gpr .r2, t.gpr .r3, t.gpr .lr)) ==
  some (7, 9, 0xdeadbeef, 0xdeadbeef)

/-! ## Printing -/

#guard printer.instr (.mul .r0 .r1 .r2) == ["mul r0, r1, r2"]
#guard printer.instr (.mul .r12 .lr .r7) == ["mul r12, lr, r7"]

-- In the ARMv7-A baseline.
#guard isa.requires (.mul .r0 .r1 .r2) == []

end VG.Test.ArmMul
